package com.github.kory33.proof.set.foundation

import com.github.kory33.proof.logic.predicate._
import com.github.kory33.proof.logic.propositional.LogicDefinitions._

import com.github.kory33.proof.set.BasicPredicates

object ZF {

    trait Existence extends SetAxiom {
        import language._
        def existence: ∃[[x] => x =::= x]
    }

    trait Extensionality extends SetAxiom {
        import language._
        def extensionality: ∀[[x] => ∀[[y] => ∀[[z] => (z ∈ x) <=> (z ∈ y)] => (x =::= y)]]
    }

    trait Separation extends SetAxiom {
        import language._
        def separation[F[_]]: ∀[[x] => ∃[[y] => ∀[[u] => (u ∈ y) <=> ((u ∈ x) ∧ F[u])]]]
    }

    trait Pairing extends SetAxiom {
        import language._
        def pairing: ∀[[x] => ∃[[y] => ∃[[z] => (x ∈ z) ∧ (y ∈ z)]]]
    }

    trait Union extends SetAxiom {
        import language._
        def union: ∀[[F] => ∃[[U] => ∀[[X] => ∀[[x] => ((x ∈ X) ∧ (X ∈ F)) => (x ∈ U)]]]]
    }

    trait Power extends SetAxiom {
        import language._
        val predicates = new BasicPredicates { val language: Power.this.language.type = Power.this.language }; import predicates._

        def power: ∀[[X] => ∃[[P] => ∀[[z] => (z ⊂ X) => (z ∈ P)]]]
    }

    trait Infinity extends SetAxiom {
        import language._
        val predicates = new BasicPredicates { val language: Infinity.this.language.type = Infinity.this.language }; import predicates._

        def infinity: ∃[[x] => ∀[[z] => isEmpty[z] => (z ∈ x)] ∧ ∀∈[x, [y] => ∀[[z] => (z isSucc y) => (z ∈ x)]]]
    }

    trait Replacement extends SetAxiom {
        import language._
        val predicates = new BasicPredicates { val language: Replacement.this.language.type = Replacement.this.language }; import predicates._

        def replacement[F[_, _]]: ∀[[A] => ∀∈[A, [x] => ∃![[y] => F[x, y]]] => ∃[[Y] => ∀∈[A, [x] => ∃∈[Y, [y] => F[x, y]]]]]
    }

    trait Regularity extends SetAxiom {
        import language._
        val predicates = new BasicPredicates { val language: Regularity.this.language.type = Regularity.this.language }; import predicates._

        def regularity: ∀[[x] => ￢[isEmpty[x]] => ∃∈[x, [y] => ￢[∃∈[x, [z] => z ∈ y]]]]
    }

    type Axioms =
        Existence &
        Extensionality &
        Separation &
        Pairing &
        Union &
        Power &
        Infinity &
        Replacement &
        Regularity

    def existence(implicit e: Existence) = e.existence
    def extensionality(implicit e: Extensionality) = e.extensionality
    def separation[F[_]](implicit s: Separation) = s.separation[F]
    def pairing(implicit p: Pairing) = p.pairing
    def union(implicit u: Union) = u.union
    def power(implicit p: Power) = p.power
    def infinity(implicit i: Infinity) = i.infinity
    def replacement[F[_, _]](implicit r: Replacement) = r.replacement[F]
    def regularity(implicit r: Regularity) = r.regularity

}
