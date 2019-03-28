package com.github.kory33.proof.set.foundation

import com.github.kory33.proof.logic.predicate._
import com.github.kory33.proof.logic.propositional.LogicDefinitions._

import com.github.kory33.proof.set.BasicPredicates

object ZF {

  trait Union extends SetAxiom {
    import context._
    val union: ∀[[F] => ∃[[U] => ∀[[X] => ∀[[x] => ((x ∈ X) ∧ (X ∈ F)) => (x ∈ U)]]]]
  }

  trait Power extends SetAxiom {
    import context._
    val predicates = new BasicPredicates { val context: Power.this.context.type = Power.this.context }; import predicates._

    val power: ∀[[X] => ∃[[P] => ∀[[z] => (z ⊂ X) => (z ∈ P)]]]
  }

  trait Infinity extends SetAxiom {
    import context._
    val predicates = new BasicPredicates { val context: Infinity.this.context.type = Infinity.this.context }; import predicates._

    val infinity: ∃[[x] => ∀[[z] => isEmpty[z] => (z ∈ x)] ∧ ∀∈[x, [y] => ∀[[z] => (z isSucc y) => (z ∈ x)]]]
  }

  trait Replacement extends SetAxiom {
    import context._
    val predicates = new BasicPredicates { val context: Replacement.this.context.type = Replacement.this.context }; import predicates._

    /**
     * This axiom is stronger than the axiom schema of replacement that is considered in an usual context.
     * Under Union & Power & Infinity, this schema is equivalent to (Normal Replacement) & Subset, or equivalently, (Normal Replacement) & Empty.
     */
    def replacement[F[_, _]]: ∀[[A] => ∀∈[A, [x] => ExistsAtMostOne[[y] => F[x, y]]] => ∃[[Y] => ∀∈[Y, [y] => ∃∈[A, [x] => F[x, y]]]]]
  }

  trait Regularity extends SetAxiom {
    import context._
    val predicates = new BasicPredicates { val context: Regularity.this.context.type = Regularity.this.context }; import predicates._

    val regularity: ∀[[x] => ￢[isEmpty[x]] => ∃∈[x, [y] => ￢[∃∈[x, [z] => z ∈ y]]]]
  }

  type Axioms =
    Union &
    Power &
    Infinity &
    Replacement &
    Regularity

}
