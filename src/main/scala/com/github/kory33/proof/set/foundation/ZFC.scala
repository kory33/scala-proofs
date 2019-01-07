package com.github.kory33.proof.set.foundation

import com.github.kory33.proof.logic.predicate._
import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.set.Predicates

object ZFC {

    trait Choice {
        val language: SetLanguage; import language._
        val predicates: Predicates { val language: Choice.this.language.type } = new Predicates { val language: Choice.this.language.type = Choice.this.language }; import predicates._
        def choice: ∀[λ[F => (hasNonemptySets[F] ∧ hasDisjointSets[F]) => ∃[λ[S => ∀∈[F, λ[X => ∃![λ[z => (z ∈ S) ∧ (z ∈ X)]]]]]]]]
    }

}

trait ZFCAxioms extends ZFAxioms {

    val axiomChoice: ZFC.Choice { val language: systemLanguage.type }

}
