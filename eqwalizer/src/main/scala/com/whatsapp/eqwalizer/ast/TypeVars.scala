/* Copyright (c) Meta Platforms, Inc. and affiliates. All rights reserved.
 *
 * This source code is licensed under the Apache 2.0 license found in
 * the LICENSE file in the root directory of this source tree.
 */

package com.whatsapp.eqwalizer.ast

import com.whatsapp.eqwalizer.ast.Types._

object TypeVars {

  def hasTypeVars(ty: Type): Boolean = ty match {
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

  /** Check that two function types have compatible forall quantifiers for subtyping comparison.
    * With De Bruijn indices, bound variables are already canonical, so we just check sizes match.
    */
  def conformForalls(ft1: FunType, ft2: FunType): Option[(FunType, FunType)] =
    if (ft1.forall.size != ft2.forall.size || ft1.argTys.size != ft2.argTys.size) None
    else Some((ft1, ft2))

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
