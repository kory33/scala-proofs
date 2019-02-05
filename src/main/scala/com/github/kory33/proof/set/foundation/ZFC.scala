package com.github.kory33.proof.set.foundation

import com.github.kory33.proof.logic.predicate._
import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.set.BasicPredicates

object ZFC {

  trait Choice extends SetAxiom {
      import language._
      val predicates = new BasicPredicates { val language: Choice.this.language.type = Choice.this.language }; import predicates._
      def choice: ∀[[F] => (hasNonemptySets[F] ∧ hasDisjointSets[F]) => ∃[[S] => S isSelectorOn F]]
  }

}

trait ZFCAxioms extends ZFAxioms {
  val axiomChoice: ZFC.Choice { val language: ZFCAxioms.this.language.type }
}
