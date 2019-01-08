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
        val predicates: Predicates { val language: Infinity.this.language.type } = new Predicates { val language: Infinity.this.language.type = Infinity.this.language }; import predicates._

        def infinity: ∃[λ[x => ∀[λ[z => isEmpty[z] => (z ∈ x)]] ∧ ∀∈[x, λ[y => ∀[λ[z => (z isSingletonOf y) => (z ∈ x)]]]]]]
    }

    trait Replacement {
        val language: SetLanguage; import language._
        val predicates: Predicates { val language: Replacement.this.language.type } = new Predicates { val language: Replacement.this.language.type = Replacement.this.language }; import predicates._

        def replacement[F[_, _]]: ∀[λ[A => ∀[λ[p => ∀∈[A, λ[x => ∃![λ[y => F[x, y]]]]] => ∃[λ[Y => ∀∈[A, λ[x => ∃∈[Y, λ[y => F[x, y]]]]]]]]]]]
    }

    trait Regularity {
        val language: SetLanguage; import language._
        val predicates: Predicates { val language: Regularity.this.language.type } = new Predicates { val language: Regularity.this.language.type = Regularity.this.language }; import predicates._

        def infinity: ∀[λ[x => ￢[isEmpty[x]] => ∃∈[x, λ[y => ￢[∃∈[x, λ[z => z ∈ y]]]]]]]
    }

}

trait ZFAxioms {

    val language: SetLanguage

    val axiomExistence: ZF.Existence { val language: ZFAxioms.this.language.type }
    val axiomExtensionality: ZF.Extensionality { val language: ZFAxioms.this.language.type }
    val axiomSeparation: ZF.Separation { val language: ZFAxioms.this.language.type }
    val axiomPairing: ZF.Pairing { val language: ZFAxioms.this.language.type }
    val axiomUnion: ZF.Union { val language: ZFAxioms.this.language.type }
    val axiomPower: ZF.Power { val language: ZFAxioms.this.language.type }
    val axiomInfinity: ZF.Infinity { val language: ZFAxioms.this.language.type }
    val axiomReplacement: ZF.Replacement { val language: ZFAxioms.this.language.type }
    val axiomRegularity: ZF.Regularity { val language: ZFAxioms.this.language.type }

}