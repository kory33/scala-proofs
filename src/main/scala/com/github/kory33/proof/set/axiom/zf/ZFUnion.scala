package com.github.kory33.proof.set.axiom.zf

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.Equality._
import com.github.kory33.proof.set._
import com.github.kory33.proof.set.SetDefinitions._

/**
  * Axiom of union.
  *
  * For every family F there exists a set U containing all elements of F.
  */
trait ZFUnion {
  def union: ∀[[F <: Σ] => ∃[[u <: Σ] => ∀[[y <: Σ] => ∀[[x <: Σ] => ((x ∈ y) ∧ (y ∈ F)) => x ∈ u]]]]
}
