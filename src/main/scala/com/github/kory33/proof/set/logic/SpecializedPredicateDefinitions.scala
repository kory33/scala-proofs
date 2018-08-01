package com.github.kory33.proof.set.logic

import com.github.kory33.proof.logic.predicate.PredicateLogicDefinitions.{∃, ∀}
import com.github.kory33.proof.set.Σ
import com.github.kory33.proof.logic.propositional.LogicDefinitions.￢

object SpecializedPredicateDefinitions {
  type ∃[F[_ <: Σ]] = com.github.kory33.proof.logic.predicate.PredicateLogicDefinitions.∃[Σ, F]
  type ∀[F[_ <: Σ]] = ￢[∃[[x <: Σ] => ￢[F[x]]]]
  trait ∃~>[P[_[_ <: Σ] <: Σ]] {
    type F[_ <: Σ] <: Σ
    val value: P[F]
  }
}