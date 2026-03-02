/* Copyright (c) Meta Platforms, Inc. and affiliates. All rights reserved.
 *
 * This source code is licensed under the Apache 2.0 license found in
 * the LICENSE file in the root directory of this source tree.
 */

package com.whatsapp.eqwalizer.tc

import com.whatsapp.eqwalizer.ast.Exprs.*
import com.whatsapp.eqwalizer.ast.Types.*
import com.whatsapp.eqwalizer.tc.TcDiagnostics.{AmbiguousLambda, ExpectedSubtype}
import com.whatsapp.eqwalizer.tc.generics.Constraints
import com.whatsapp.eqwalizer.tc.generics.Constraints.ConstraintSeq

import scala.collection.mutable.ListBuffer

/** Implement Pierce and Turner "Local Type Inference" with the following tweaks:
  * - special handling for functions applied to lambdas, see `synthesizeWithLambdas`
  * - instantiation of polymorphic function args via constraint solving - see `PolyFunArg` and `instantiatePoly`
  * - no special handling for generic function application in check mode: we didn't see much difference in behavior
  * and it's easier to maintain fewer code paths. P&T say the special casing helps for when there are type vars in
  * return types that appear in both positive and negative positions.
  * - A single code path for both generic and non-generic function application
  */
class ElabApply(pipelineContext: PipelineContext) {
  private lazy val check = pipelineContext.check
  private lazy val elab = pipelineContext.elab
  private lazy val subtype = pipelineContext.subtype
  private lazy val constraints = pipelineContext.constraints
  private lazy val occurrence = pipelineContext.occurrence
  private lazy val narrow = pipelineContext.narrow
  private lazy val variance = pipelineContext.variance
  private lazy val typeInfo = pipelineContext.typeInfo
  private lazy val diagnosticsInfo = pipelineContext.diagnosticsInfo
  implicit val pipelineCtx: PipelineContext = pipelineContext

  private type Var = Int

  private sealed trait AppliedArg extends Constraints.ConstraintLoc
  private case class LambdaArg(arg: Lambda, argTy: Type, paramTy: FunType) extends AppliedArg
  private case class PolyFunArg(arg: Expr, argTy: FunType, paramTy: Type) extends AppliedArg
  private case class Arg(arg: Expr, argTy: Type, paramTy: Type) extends AppliedArg

  // detailled docs in ./generics/README.md
  def elabApply(ft: FunType, args: List[Expr], argTys: List[Type], env: Env): Type = {

    assert(ft.argTys.size == argTys.size)
    assert(args.size == argTys.size)

    val toSolve = ft.forall.toSet

    def lambdaArg(lambda: Lambda, argTy: FunType, paramTy: Type): AppliedArg = {
      val arity = lambda.clauses.headOption.map(_.pats.size).getOrElse(0)
      val funParamTys = narrow.onlyFunTypes(paramTy, arity)
      if (funParamTys.size == 1) {
        LambdaArg(lambda, argTy, funParamTys.head)
      } else if (funParamTys.size > 1) {
        diagnosticsInfo.add(AmbiguousLambda(lambda.pos, lambda, subtype.join(funParamTys)))
        LambdaArg(lambda, argTy, FunType(List(), List.fill(arity)(DynamicType), DynamicType))
      } else {
        paramTy match {
          // Keep it as a LambdaArg to produce an arity mismatch error message, which provides clearer signal
          case ft: FunType => LambdaArg(lambda, argTy, ft)
          case t if subtype.gradualSubType(DynamicType, t) =>
            LambdaArg(lambda, argTy, FunType(List(), List.fill(arity)(DynamicType), DynamicType))
          case _ => Arg(lambda, argTy, paramTy)
        }
      }
    }

    val appliedArgs = args
      .zip(argTys)
      .zip(ft.argTys)
      .map {
        case ((lambda: Lambda, argTy: FunType), paramTy) if argTy.argTys.nonEmpty =>
          lambdaArg(lambda, argTy, paramTy)
        case ((fun: LocalFun, argTy: FunType), paramTy) if argTy.forall.nonEmpty =>
          PolyFunArg(fun, argTy, paramTy)
        case ((fun: RemoteFun, argTy: FunType), paramTy) if argTy.forall.nonEmpty =>
          PolyFunArg(fun, argTy, paramTy)
        case ((expr, argTy), paramTy) => Arg(expr, argTy, paramTy)
      }

    val lambdaArgs = appliedArgs.collect { case la: LambdaArg => la }
    val polyFunArgs = appliedArgs.collect { case pa: PolyFunArg => pa }
    val nonLambdaArgs = appliedArgs.collect { case pa: Arg => pa }

    val variances = variance.toVariances(ft)
    val delayed: ListBuffer[Arg] = ListBuffer.empty
    val cs0 = nonLambdaArgs.foldLeft(Vector.empty: ConstraintSeq) { case (cs, arg) =>
      try
        constraints.constraintGen(
          toSolve,
          cs = cs,
          variances = variances,
          lowerBound = arg.argTy,
          upperBound = arg.paramTy,
          constraintLoc = arg,
          tolerateUnion = true,
        )
      catch {
        case Constraints.UnionFailure() =>
          delayed.addOne(arg)
          cs
      }
    }

    // We generate constraints from the non-lambda args and find a substitution that minimizes type vars in ft.resTy
    val m0 = constraints.meetAllConstraints(cs0, variances, Map.empty)
    val subst0 = constraints.constraintsToSubst(m0, variances)

    val cs1 = delayed.toList.foldLeft(cs0) { case (cs, arg) =>
      constraints.constraintGen(
        toSolve,
        cs = cs,
        variances = variances,
        lowerBound = arg.argTy,
        upperBound = Subst.subst(subst0, arg.paramTy),
        constraintLoc = arg,
        tolerateUnion = false,
      )
    }

    val m1 = constraints.meetAllConstraints(cs1, variances, m0)
    val subst1 = constraints.constraintsToSubst(m1, variances, toSolve)

    // Instantiate polymorphic function args using the partial substitution
    val cs2 = polyFunArgs.foldLeft(cs1) { case (cs, polyArg) =>
      val resolvedParamTy = Subst.subst(subst1, polyArg.paramTy)
      val pairs = polyArg.argTy.argTys.zip(
        narrow
          .onlyFunTypes(resolvedParamTy, polyArg.argTy.argTys.size)
          .headOption
          .map(_.argTys)
          .getOrElse(List.fill(polyArg.argTy.argTys.size)(DynamicType))
      ).map { case (polyParam, expectedParam) => (expectedParam, polyParam) }
      constraints.instantiatePoly(polyArg.argTy, pairs) match {
        case Some(monoFt) =>
          constraints.constraintGen(
            toSolve,
            cs = cs,
            variances = variances,
            lowerBound = monoFt,
            upperBound = resolvedParamTy,
            constraintLoc = Arg(polyArg.arg, monoFt, polyArg.paramTy),
            tolerateUnion = false,
          )
        case None => cs
      }
    }

    val m2 = constraints.meetAllConstraints(cs2, variances, m1)
    val subst2 = constraints.constraintsToSubst(m2, variances, toSolve)

    // Then we check the lambdas and use the inferred return types of the lambdas for a final round of constraint generation
    def inferenceRound(cs: ConstraintSeq, subst: Map[Var, Type]): (ConstraintSeq, Map[Var, Type]) = {
      val cs1 = lambdaArgs.foldLeft(cs) { case (cs, lambdaArg) =>
        val resolved = lambdaToFunTy(lambdaArg, subst, env)
        constraints.constraintGen(
          toSolve,
          cs = cs,
          variances = variances,
          lowerBound = resolved.resTy,
          upperBound = lambdaArg.paramTy.resTy,
          constraintLoc = lambdaArg.copy(argTy = resolved),
          tolerateUnion = false,
        )
      }
      val subst1 = constraints.constraintsSeqToSubst(cs1, variances, toSolve)
      (cs1, subst1)
    }

    val (cs4, subst4) = typeInfo.withoutTypeCollection {
      val (cs3, subst3) = inferenceRound(cs2, subst2)
      val subst3Merged = subst3.map {
        case (v, UnionType(tys)) => (v, narrow.joinAndMergeMaps(tys))
        case (v, ty)             => (v, ty)
      }
      inferenceRound(cs3, subst3Merged)
    }

    // Then we check the lambdas and use the inferred return types of the lambdas for a final round of constraint generation

    // We check that all arguments are well-typed under the final substitution.
    // These checks are necessary because:
    // - A type can be both an input and an output of a lambda.
    // - (optimization) We exit constraint generation early if there are no type variables: in such cases we still need to check
    // that the args match the parameters.
    // - We assume that any consistent substitution of type variables is sound.
    //   For example, we use an approximation for `meet` in Constraints.scala
    nonLambdaArgs.foreach(checkArg(_, subst4))
    polyFunArgs.foreach(checkPolyFunArg(_, subst4))
    lambdaArgs.foreach(checkLambdaArg(_, subst4, env))

    Subst.subst(subst4, ft.resTy)
  }

  private def checkArg(arg: Arg, varToType: Map[Var, Type]): Unit = {
    val Arg(expr, argTy, rawParamTy) = arg
    val paramTy = Subst.subst(varToType, rawParamTy)
    if (!subtype.subType(argTy, paramTy))
      diagnosticsInfo.add(ExpectedSubtype(expr.pos, expr, expected = paramTy, got = argTy))
  }

  private def checkPolyFunArg(polyArg: PolyFunArg, varToType: Map[Var, Type]): Unit = {
    val paramTy = Subst.subst(varToType, polyArg.paramTy)
    if (!subtype.subType(polyArg.argTy, paramTy))
      diagnosticsInfo.add(ExpectedSubtype(polyArg.arg.pos, polyArg.arg, expected = paramTy, got = polyArg.argTy))
  }

  private def checkLambdaArg(lambdaArg: LambdaArg, varToType: Map[Var, Type], env: Env): Unit = {
    val LambdaArg(lambda, _, FunType(_, rawArgTys, rawExpResTy)) = lambdaArg
    val argTys = rawArgTys.map(Subst.subst(varToType, _))
    val expResTy = Subst.subst(varToType, rawExpResTy)
    val expFunTy = FunType(Nil, argTys, expResTy)
    val env1 =
      lambda.name match {
        case Some(name) =>
          val funType = FunType(Nil, List.fill(argTys.size)(DynamicType), DynamicType)
          env.updated(name, funType)
        case _ =>
          env
      }
    check.checkLambda(lambda, expFunTy, env1)
  }

  private def lambdaToFunTy(
      lambdaArg: LambdaArg,
      varToType: Map[Var, Type],
      env: Env,
  ): FunType = {
    val LambdaArg(lambda, _, ft: FunType) = lambdaArg

    val argTys = ft.argTys.map(Subst.subst(varToType, _))
    val env1 =
      lambda.name match {
        case Some(name) =>
          val funType = FunType(Nil, List.fill(argTys.size)(DynamicType), DynamicType)
          env.updated(name, funType)
        case _ =>
          env
      }

    val envs = occurrence.clausesEnvs(lambda.clauses, argTys, env1)
    val clauseTys =
      lambda.clauses
        .lazyZip(envs)
        .map((clause, occEnv) => elab.elabClause(clause, argTys, occEnv, Set.empty))
        .map(_._1)

    val resTy = subtype.join(clauseTys)
    ft.copy(argTys = argTys, resTy = resTy)
  }
}
