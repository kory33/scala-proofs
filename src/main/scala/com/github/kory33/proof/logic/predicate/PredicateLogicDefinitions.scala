package com.github.kory33.proof.logic.predicate

import com.github.kory33.proof.logic.propositional.LogicDefinitions.￢

object PredicateLogicDefinitions {

  type ∀[F[_]] = ￢[∃[({ type λ[A] = ￢[F[A]] })#λ]]

  type ∃[F[_]] = F[_]

}
