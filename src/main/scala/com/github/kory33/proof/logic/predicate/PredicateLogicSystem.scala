package com.github.kory33.proof.logic.predicate

import com.github.kory33.proof.logic.predicate.PredicateLogicDefinitions.{∀, ∃}
import com.github.kory33.proof.logic.propositional.ClassicalLogicAxiom
import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._

object PredicateLogicSystem {

  def existential[φ](implicit
                     classicalLogicAxiom: ClassicalLogicAxiom,
                     predicateLogicAxiom: PredicateLogicAxiom): φ ≣ ∃[({ type λ[X] = φ })#λ] = {
    val implies = { ev: φ =>
      byContradiction { assumption: ∀[({ type λ[A] = ￢[φ] })#λ] =>
        val r = predicateLogicAxiom.universal[￢[φ]].impliedBy.apply(assumption)
        ev ∧ r
      }
    }

    val impliedBy = { existEv: ∃[({ type λ[A] = φ })#λ] =>
      classicalLogicAxiom.eliminateDoubleNegation(
        contraposition(predicateLogicAxiom.universal[￢[φ]].implies)(existEv)
      )
    }

    implies ∧ impliedBy
  }

}
