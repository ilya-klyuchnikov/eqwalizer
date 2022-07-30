/* Copyright (c) Meta Platforms, Inc. and affiliates. All rights reserved.
 *
 * This source code is licensed under the Apache 2.0 license found in
 * the LICENSE file in the root directory of this source tree.
 */

package com.whatsapp.eqwalizer.tc

import com.whatsapp.eqwalizer.ast.Exprs._
import com.whatsapp.eqwalizer.ast.Pats.PatVar
import com.whatsapp.eqwalizer.ast.Types._
import com.whatsapp.eqwalizer.tc.TcDiagnostics.ExpectedSubtype
import com.whatsapp.eqwalizer.tc.generics.{Constraints, Variance}
import com.whatsapp.eqwalizer.tc.generics.Constraints.ConstraintSeq

/** Implement Pierce and Turner "Local Type Inference" with the following tweaks:
  * - special handling for functions applied to lambdas, see `synthesizeWithLambdas`
  * - instantiation of generic functions through eta-expansion - see `etaExpand`
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
  implicit val pipelineCtx = pipelineContext

  private type Var = Int

  private sealed trait AppliedArg extends Constraints.ConstraintLoc
  private case class LambdaArg(arg: Lambda, argTy: Type, paramTy: FunType) extends AppliedArg
  private case class Arg(arg: Expr, argTy: Type, paramTy: Type) extends AppliedArg

  private def etaExpand(fun: LocalFun): Lambda = {
    val pos = fun.pos
    val varNames = (1 to fun.id.arity).map(n => s"Arg $n of '${fun.id}'").toList
    val vars = varNames.map(Var(_)(pos))
    val patVars = varNames.map(PatVar(_)(pos))
    val app = LocalCall(fun.id, vars)(pos)
    val clause = Clause(patVars, Nil, Body(List(app)))(pos)
    Lambda(List(clause))(pos, name = None)
  }
  private def etaExpand(fun: RemoteFun): Lambda = {
    val pos = fun.pos
    val varNames = (1 to fun.id.arity).map(n => s"Arg $n of '${fun.id}'").toList
    val patVars = varNames.map(PatVar(_)(pos))
    val vars = varNames.map(Var(_)(pos))
    val app = RemoteCall(fun.id, vars)(pos)
    val clause = Clause(patVars, Nil, Body(List(app)))(pos)
    Lambda(List(clause))(pos, name = None)
  }

  // detailled docs in ./generics/README.md
  def elabApply(ft: FunType, args: List[Expr], argTys: List[Type], env: Env): Type = {

    assert(ft.argTys.size == argTys.size)
    assert(args.size == argTys.size)

    val toSolve = ft.forall.toSet

    val appliedArgs = args
      .zip(argTys)
      .zip(ft.argTys)
      .map {
        case ((lambda: Lambda, argTy: FunType), paramTy: FunType) if argTy.argTys.nonEmpty =>
          LambdaArg(lambda, argTy, paramTy)
        case ((fun: LocalFun, argTy: FunType), paramTy: FunType) if argTy.forall.nonEmpty =>
          LambdaArg(etaExpand(fun), argTy, paramTy)
        case ((fun: RemoteFun, argTy: FunType), paramTy: FunType) if argTy.forall.nonEmpty =>
          LambdaArg(etaExpand(fun), argTy, paramTy)
        case ((expr, argTy), paramTy) => Arg(expr, argTy, paramTy)
      }

    val lambdaArgs = appliedArgs.collect { case la: LambdaArg => la }
    val nonLambdaArgs = appliedArgs.collect { case pa: Arg => pa }

    val variances = Variance.toVariances(ft)
    val cs1 = nonLambdaArgs.foldLeft(Vector.empty: ConstraintSeq) { case (cs, arg) =>
      constraints.constraintGen(
        toSolve,
        cs = cs,
        variances = variances,
        lowerBound = arg.argTy,
        upperBound = arg.paramTy,
        constraintLoc = arg,
      )
    }

    // We generate constraints from the non-lambda args and find a substitution that minimizes type vars in ft.resTy
    val subst1 = constraints.constraintsSeqToSubst(cs1, variances, toSolve)

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
        )
      }
      val subst1 = constraints.constraintsSeqToSubst(cs1, variances, toSolve)
      (cs1, subst1)
    }

    val (cs2, subst2) = inferenceRound(cs1, subst1)
    val (cs3, subst3) = inferenceRound(cs2, subst2)

    // Then we check the lambdas and use the inferred return types of the lambdas for a final round of constraint generation

    // We check that all arguments are well-typed under the final substitution.
    // These checks are necessary because:
    // - A type can be both an input and an output of a lambda.
    // - (optimization) We exit constraint generation early if there are no type variables: in such cases we still need to check
    // that the args match the parameters.
    // - We assume that any consistent substitution of type variables is sound.
    //   For example, we use an approximation for `meet` in Constraints.scala
    nonLambdaArgs.foreach(checkArg(_, subst3))
    lambdaArgs.foreach(checkLambdaArg(_, subst3, env))

    Subst.subst(subst3, ft.resTy)
  }

  private def checkArg(arg: Arg, varToType: Map[Var, Type]): Unit = {
    val Arg(expr, argTy, rawParamTy) = arg
    val paramTy = Subst.subst(varToType, rawParamTy)
    if (!subtype.subType(argTy, paramTy))
      throw ExpectedSubtype(expr.pos, expr, expected = paramTy, got = argTy)
  }

  private def checkLambdaArg(lambdaArg: LambdaArg, varToType: Map[Var, Type], env: Env): Unit = {
    val LambdaArg(lambda, _, FunType(_, rawArgTys, rawExpResTy)) = lambdaArg
    val argTys = rawArgTys.map(Subst.subst(varToType, _))
    val expResTy = Subst.subst(varToType, rawExpResTy)
    val expFunTy = FunType(Nil, argTys, expResTy)
    val env1 =
      lambda.name match {
        case Some(name) if pipelineCtx.gradualTyping =>
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
        case Some(name) if pipelineCtx.gradualTyping =>
          val funType = FunType(Nil, List.fill(argTys.size)(DynamicType), DynamicType)
          env.updated(name, funType)
        case _ =>
          env
      }

    val clauseTys =
      if (occurrence.eqwater(lambda.clauses)) {
        val envs = occurrence.clausesEnvs(lambda.clauses, argTys, env1)
        lambda.clauses
          .lazyZip(envs)
          .map((clause, occEnv) => elab.elabClause(clause, argTys, occEnv, Set.empty))
          .map(_._1)
      } else
        lambda.clauses.map(elab.elabClause(_, argTys, env1, Set.empty)).map(_._1)

    val resTy = subtype.join(clauseTys)
    ft.copy(argTys = argTys, resTy = resTy)
  }
}
