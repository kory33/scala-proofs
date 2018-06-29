package com.github.kory33.proof.logic.predicate

import com.github.kory33.proof.logic.propositional.LogicDefinitions.￢

object PredicateLogicDefinitions {

  type ∀[F[_]] = F[_]

  type ∃[F[_]] = ￢[∀[({ type λ[A] = ￢[F[A]] })#λ]]

  /* With type lambdas

  type ∃[F[_]] = ￢[∀[X :-> ￢[F[X]]]]

   */

}
