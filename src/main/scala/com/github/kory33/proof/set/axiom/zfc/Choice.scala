package com.github.kory33.proof.set.axiom.zfc

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.Equality._
import com.github.kory33.proof.set._
import com.github.kory33.proof.set.SetDefinitions._

/**
  * For every family F of disjoint nonempty sets there exists a selector S that intersects every x ∈ F in precisely one point.
  */
trait Choice {
  def choice: ∀[[F <: Σ] => ((F hasAll ([x <: Σ] => ￢[isEmpty[x]])) ∧ isPairwiseDisjoint[F]) => ∃[[S <: Σ] => S isASelectorOn F]]
}