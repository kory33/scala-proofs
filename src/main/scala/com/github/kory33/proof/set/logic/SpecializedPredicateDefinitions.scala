package com.github.kory33.proof.set.logic

import com.github.kory33.proof.logic.predicate.PredicateLogicDefinitions.{∃, ∀}
import com.github.kory33.proof.logic.propositional.LogicDefinitions.￢

/**
 * Domain of discourse of set theory.
 */
trait SetDomain[x] private ()

object SpecializedPredicateDefinitions {
  type ∃[F[_]] = com.github.kory33.proof.logic.predicate.PredicateLogicDefinitions.∃[SetDomain, F]
  type ∀[F[_]] = ￢[∃[[x] => ￢[F[x]]]]
  trait ∃~>[P[_[_]]] {
    type F[_]

    val instance: P[F]
    def typeclass[X : SetDomain]: SetDomain[F[X]]
  }
  trait ∃~~>[P[_[_, _]]] {
    type F[_, _]

    val instance: P[F]
    def typeclass[X : SetDomain, Y : SetDomain]: SetDomain[F[X, Y]]
  }
}
