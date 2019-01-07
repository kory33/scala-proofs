package com.github.kory33.proof.set.foundation

import com.github.kory33.proof.logic.predicate._
import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.set.Predicates

object ZF {

    trait Existence {
        val language: SetLanguage; import language._
        def existence: ∃[λ[x => x =::= x]]
    }

    trait Extensionality {
        val language: SetLanguage; import language._
        def extensionality: ∀[λ[x => ∀[λ[y => ∀[λ[z => (z ∈ x) <=> (z ∈ y)]] => (x =::= y)]]]]
    }

    trait Separation {
        val language: SetLanguage; import language._
        def separation[F[_]]: ∀[λ[x => ∃[λ[y => ∀[λ[u => (u ∈ y) <=> ((u ∈ x) ∧ F[u])]]]]]]
    }

    trait Pairing {
        val language: SetLanguage; import language._
        def pairing: ∀[λ[x => ∃[λ[y => ∃[λ[z => (x ∈ z) ∧ (y ∈ z)]]]]]]
    }

    trait Union {
        val language: SetLanguage; import language._
        def union: ∀[λ[F => ∃[λ[U => ∀[λ[X => ∀[λ[x => ((x ∈ X) ∧ (X ∈ F)) => (x ∈ U)]]]]]]]]
    }

    trait Power {
        val language: SetLanguage; import language._
        val predicates: Predicates { val language: Power.this.language.type } = new Predicates { val language: Power.this.language.type = Power.this.language }; import predicates._

        def power: ∀[λ[X => ∃[λ[P => ∀[λ[z => (z ⊂ X) => (z ∈ P)]]]]]]
    }

    trait Infinity {
        val language: SetLanguage; import language._
    }

    trait Replacement {
        val language: SetLanguage; import language._
    }

    trait Regularity {
        val language: SetLanguage; import language._
    }

}

trait ZFAxioms {

    val systemLanguage: SetLanguage

    val axiomExistence: ZF.Existence { val language: systemLanguage.type }
    val axiomExtensionality: ZF.Extensionality { val language: systemLanguage.type }
    val axiomSeparation: ZF.Separation { val language: systemLanguage.type }
    val axiomPairing: ZF.Pairing { val language: systemLanguage.type }
    val axiomUnion: ZF.Union { val language: systemLanguage.type }
    val axiomPower: ZF.Power { val language: systemLanguage.type }
    val axiomInfinity: ZF.Infinity { val language: systemLanguage.type }
    val axiomReplacement: ZF.Replacement { val language: systemLanguage.type }
    val axiomRegularity: ZF.Regularity { val language: systemLanguage.type }

}