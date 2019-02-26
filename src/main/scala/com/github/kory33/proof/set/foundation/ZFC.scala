package com.github.kory33.proof.set.foundation

import com.github.kory33.proof.logic.predicate._
import com.github.kory33.proof.logic.propositional.LogicDefinitions._

import com.github.kory33.proof.set.BasicPredicates

trait ZFC {

  trait Choice extends SetAxiom {
      import language._
      val predicates = new BasicPredicates { val language: Choice.this.language.type = Choice.this.language }; import predicates._
      def choice: ∀[[F] => (hasNonemptySets[F] ∧ hasDisjointSets[F]) => ∃[[S] => S isSelectorOn F]]
  }

  type Axioms = ZF.Axioms & Choice

  def choice(implicit c: Choice) = c.choice

}
