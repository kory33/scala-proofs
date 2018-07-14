package com.github.kory33.proof.set.logic

import com.github.kory33.proof.logic.predicate.PredicateLogicDefinitions.{∃, ∀}
import com.github.kory33.proof.set.AxiomaticSet
import com.github.kory33.proof.logic.propositional.LogicDefinitions.￢

object SpecializedPredicateDefinitions {
  type ∃[F[_ <: AxiomaticSet]] = com.github.kory33.proof.logic.predicate.PredicateLogicDefinitions.∃[AxiomaticSet, F]
  type ∀[F[_ <: AxiomaticSet]] = ￢[∃[[x <: AxiomaticSet] => ￢[F[x]]]]
}