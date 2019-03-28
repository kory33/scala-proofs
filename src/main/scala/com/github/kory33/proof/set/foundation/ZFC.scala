package com.github.kory33.proof.set.foundation

import com.github.kory33.proof.logic.predicate._
import com.github.kory33.proof.logic.propositional.LogicDefinitions._

import com.github.kory33.proof.set.BasicPredicates

trait ZFC {

  trait Choice extends SetAxiom {
    import context._
    val predicates = new BasicPredicates { val context: Choice.this.context.type = Choice.this.context }; import predicates._
    val choice: ∀[[F] => (hasNonemptySets[F] ∧ hasDisjointSets[F]) => ∃[[S] => S isSelectorOn F]]
  }

  type Axioms = ZF.Axioms & Choice

}
