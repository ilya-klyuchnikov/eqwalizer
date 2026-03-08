/* Copyright (c) Meta Platforms, Inc. and affiliates. All rights reserved.
 *
 * This source code is licensed under the Apache 2.0 license found in
 * the LICENSE file in the root directory of this source tree.
 */

package com.whatsapp.eqwalizer.ast

import com.whatsapp.eqwalizer.ast.Types._

object TypeVars {

  class VarFreshener {
    private var counter = 0

    def freshen(ft: FunType): FunType = {
      val (ft1, newMax) = freshenFrom(ft, counter.max(maxVarInt(ft, counter)))
      val newCounter = newMax + 1
      assert(newCounter > counter)
      counter = newCounter
      ft1
    }
  }

  def hasTypeVars(ty: Type): Boolean = ty match {
    case VarType(_)  => true
    case BoundVar(_) => true
    case FreeVar(_)  => true
    case ty          => children(ty).exists(hasTypeVars)
  }

  /** note: returns Nil for record types because they can't have type vars
    */
  def children(ty: Type): List[Type] = ty match {
    case FunType(_, argTys, resTy)    => resTy :: argTys
    case AnyArityFunType(resTy)       => resTy :: Nil
    case TupleType(argTys)            => argTys
    case UnionType(tys)               => tys.toList
    case RemoteType(_, tys)           => tys
    case MapType(props, kType, vType) => kType :: vType :: props.values.map(_.tp).toList
    case ListType(ty)                 => ty :: Nil
    case RefinedRecordType(_, fields) => fields.toList.map(_._2)
    case BoundedDynamicType(bound)    => bound :: Nil
    case _                            => Nil
  }

  /** For subtyping comparison, make ft1 and ft2 such that their `forall`s quantify over variables with the same
    * numbers, in the same order. This is required by algorithms in Pierce and Turner "Local Type Inference",
    * but they don't say how to do it.
    *
    * For example, given function types:
    * `ft1 = forall(1, 2). (1, 2) -> {2, 3}`
    * `ft2 = forall(2, 3). (2, {3}) -> (2 -> 4)`
    *
    * we return something like:
    *
    * `newFt1 = forall(5, 6). (5, 6) -> {6, 3}`
    * `newFt2 = forall(5, 6). (5, {6}) -> (5 -> 4)`
    *
    * We rename all bound variables in ft1 and ft2 from the same starting integer, which is higher
    * than all the variables in ft1 and ft2. In the example above, `5` is the new starting integer,
    * so the foralls are conformed to both be List(5, 6) and the parameter and return types are updated accordingly.
    *
    * Here's why I think this is safe:
    * - No change is ever made to variables free in ft1 or ft2
    * - Renaming of bound variables will not capture free vars because
    * we ensured that min(bound vars) > max(free vars).
    */
  def conformForalls(ft1: FunType, ft2: FunType): Option[(FunType, FunType)] =
    if (ft1.forall.size != ft2.forall.size || ft1.argTys.size != ft2.argTys.size) None
    else {
      val forallStart = 1 + maxVarInt(ft1, 0).max(maxVarInt(ft2, 0))
      val (newFt1, _) = freshenFrom(ft1, forallStart)
      val (newFt2, _) = freshenFrom(ft2, forallStart)
      assert(newFt1.forall.minOption == newFt2.forall.minOption)
      Some(newFt1, newFt2)
    }

  /** Rename so that the bound variables of `ft` start from `forallStart`.
    */
  private def freshenFrom(ft: FunType, forallStart: Int): (FunType, Int) = {
    val ft1 = incrForall(ft, forallStart)
    val newMax = maxVarInt(ft1, start = forallStart)
    (ft1, newMax)
  }

  private def maxVarInt(ty: Type, start: Int): Int = {
    def maxOfChildren: Int = children(ty).foldLeft(start)((max, t) => max.max(maxVarInt(t, max)))
    ty match {
      case VarType(n) => n
      case FunType(forall, _, _) =>
        val forallMax = forall.maxOption.getOrElse(0)
        forallMax.max(maxOfChildren)
      case _ => maxOfChildren
    }
  }

  private def incrForall(ft: FunType, forallStart: Int): FunType = {
    val FunType(forall, argTys, resTy) = ft
    forall.minOption match {
      case Some(min) =>
        val incr = 1 + (forallStart - min)
        assert(incr > 0)
        val toIncr = forall.toSet
        val forall1 = ft.forall.map(_ + incr)
        val argTys1 = argTys.map(incrVars(_, toIncr, incr))
        val resTy1 = incrVars(resTy, toIncr, incr)
        FunType(forall1, argTys1, resTy1)
      case None => ft
    }
  }

  private def incrVars(t: Type, toIncr: Set[Int], incr: Int): Type = {
    def r(t: Type): Type = incrVars(t, toIncr, incr)
    t match {
      case FunType(forall, args, resType) =>
        val forall1 = forall.map(n => if (toIncr.contains(n)) n + incr else n)
        FunType(forall1, args.map(incrVars(_, toIncr, incr)), incrVars(resType, toIncr, incr))
      case AnyArityFunType(resType) =>
        AnyArityFunType(r(resType))
      case TupleType(params) =>
        TupleType(params.map(r))
      case ListType(elemT) =>
        ListType(r(elemT))
      case UnionType(params) =>
        UnionType(params.map(r))
      case RemoteType(id, params) =>
        RemoteType(id, params.map(r))
      case vt: VarType if toIncr.contains(vt.n) => VarType(vt.n + incr)(vt.name)
      case _: VarType                           => t
      case MapType(props, kt, vt) =>
        MapType(props.map { case (name, Prop(req, tp)) => (name, Prop(req, r(tp))) }, r(kt), r(vt))
      case RefinedRecordType(recType, fields) =>
        RefinedRecordType(recType, fields.map(f => f._1 -> r(f._2)))
      case _ =>
        t
    }
  }

  // --- New Bound/Free type variable operations ---

  /** Generic type variable transformation, tracking binder depth (lvl).
    * The transform function receives:
    *   - Left(i) for BoundVar(i) or Right(name) for FreeVar(name)
    *   - the current binder depth (lvl)
    *   - the original type (as default)
    * and returns a transformed type.
    */
  def typeVarTransform(ty: Type, f: (Either[Int, String], Int, Type) => Type, lvl: Int): Type = {
    def r(t: Type): Type = typeVarTransform(t, f, lvl)
    ty match {
      case bv: BoundVar =>
        f(Left(bv.i), lvl, bv)
      case fv: FreeVar =>
        f(Right(fv.name), lvl, fv)
      case FunType(forall, argTys, resTy) =>
        val newLvl = lvl + forall.size
        FunType(forall, argTys.map(typeVarTransform(_, f, newLvl)), typeVarTransform(resTy, f, newLvl))
      case AnyArityFunType(resTy) =>
        AnyArityFunType(r(resTy))
      case TupleType(argTys) =>
        TupleType(argTys.map(r))
      case ListType(t) =>
        ListType(r(t))
      case UnionType(tys) =>
        UnionType(tys.map(r))
      case RemoteType(id, tys) =>
        RemoteType(id, tys.map(r))
      case MapType(props, kType, vType) =>
        MapType(props.map { case (key, Prop(req, tp)) => (key, Prop(req, r(tp))) }, r(kType), r(vType))
      case RefinedRecordType(recType, fields) =>
        RefinedRecordType(recType, fields.map { case (k, v) => k -> r(v) })
      case BoundedDynamicType(bound) =>
        BoundedDynamicType(r(bound))
      case _ =>
        ty
    }
  }

  /** Converts FreeVar(name) to BoundVar with De Bruijn indices.
    * `names` is the list of free variable names to abstract over,
    * ordered so that names(0) gets the highest index (outermost).
    *
    * For example, abstractType(ty, List("A", "B")) converts:
    *   FreeVar("A") -> BoundVar(1)("A")
    *   FreeVar("B") -> BoundVar(0)("B")
    *
    * This matches the convention used by tr-scala.
    */
  def abstractType(initial: Type, names: List[String]): Type = {
    if (names.isEmpty) return initial
    val n1 = names.length - 1

    def transform(target: Either[Int, String], lvl: Int, default: Type): Type =
      target match {
        case Right(name) =>
          val idx = names.indexOf(name)
          if (idx >= 0) BoundVar(lvl + (n1 - idx))(name)
          else default
        case Left(_) => default
      }

    typeVarTransform(initial, transform, 0)
  }

  /** Converts BoundVar(i) to corresponding types from `images`.
    * `images` is the list of types to substitute, ordered so that
    * images(0) corresponds to the outermost (highest-index) bound variable.
    *
    * For example, instantiateType(ty, List(T1, T2)) replaces:
    *   BoundVar(1) -> T1  (the outermost)
    *   BoundVar(0) -> T2  (the innermost)
    *
    * This matches the convention used by tr-scala.
    */
  def instantiateType(initial: Type, images: List[Type]): Type = {
    if (images.isEmpty) return initial
    val n1 = images.length - 1

    def transform(target: Either[Int, String], lvl: Int, default: Type): Type =
      target match {
        case Left(idx) =>
          val adjustedIdx = n1 - (idx - lvl)
          if (adjustedIdx >= 0 && adjustedIdx < images.length)
            images(adjustedIdx)
          else
            default
        case Right(_) => default
      }

    typeVarTransform(initial, transform, 0)
  }
}
