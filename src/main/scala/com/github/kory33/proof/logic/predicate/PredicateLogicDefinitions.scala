package com.github.kory33.proof.logic.predicate

import com.github.kory33.proof.logic.propositional.LogicDefinitions.￢

object PredicateLogicDefinitions {

  trait ∃[F[_]] {
    type S
    def value: F[S]
  }

  type ∀[F[_]] = ￢[∃[[x] => ￢[F[x]]]]

}
