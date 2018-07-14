package com.github.kory33.proof.logic.predicate

import com.github.kory33.proof.logic.propositional.LogicDefinitions.￢

object PredicateLogicDefinitions {

  trait ∃[+D, F[_ <: D]] {
    type S <: D
    def value: F[S]
  }

  type ∀[-D, F[_ <: D]] = ￢[∃[D, [x <: D] => ￢[F[x]]]]

}
