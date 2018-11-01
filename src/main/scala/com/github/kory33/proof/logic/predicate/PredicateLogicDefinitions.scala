package com.github.kory33.proof.logic.predicate

import com.github.kory33.proof.logic.propositional.LogicDefinitions.￢

object PredicateLogicDefinitions {

  trait ∃[+D, F[_ <: D]] {
    type S <: D
    val value: F[S]
  }

  type ∀[D, F[_ <: D]] = ￢[∃[D, [x <: D] => ￢[F[x]]]]

  /**
   * There exists a type constructor such that F is fulfilled.
   */
  trait ∃~>[D, P[_[_ <: D] <: D]] {
    type F[_ <: D] <: D
    val value: P[F]
  }

}
