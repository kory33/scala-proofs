package com.github.kory33.proof.set

import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateSystem._
import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set.ZFAxiom

trait ZFCAxiom extends ZFAxiom {

  /**
   * For every family F of disjoint nonempty sets there exists a selector S that intersects every x ∈ F in precisely one point.
   */
  def choice: ∀[[F <: Σ] => ((F hasAll ([x <: Σ] => ￢[isEmpty[x]])) ∧ isPairwiseDisjoint[F]) => ∃[[S <: Σ] => S isASelectorOn F]]

}

object ZFCAxiom {
  def choice(implicit axiom: ZFCAxiom): ∀[[F <: Σ] => ((F hasAll ([x <: Σ] => ￢[isEmpty[x]])) ∧ isPairwiseDisjoint[F]) => ∃[[S <: Σ] => S isASelectorOn F]] = axiom.choice
}
