package com.github.kory33.experimental.proof.set.logic

import com.github.kory33.proof.logic.predicate.PredicateLogicDefinitions.{∃, ∀}
import com.github.kory33.proof.set.Σ
import com.github.kory33.proof.logic.propositional.LogicDefinitions.￢

/**
 * Domain of discourse of set theory.
 */
trait SetDomain[x] private ()

object SpecializedPredicateDefinitions {
  type ∃[F[_]] = com.github.kory33.experimental.proof.logic.predicate.PredicateLogicDefinitions.∃[SetDomain, F]
  type ∀[F[_]] = ￢[∃[[x] => ￢[F[x]]]]
}