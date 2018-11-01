package com.github.kory33.experimental.proof.set.axiom.zf

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.experimental.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.experimental.proof.logic.predicate.Equality._
import com.github.kory33.experimental.proof.set._
import com.github.kory33.experimental.proof.set.SetDefinitions._

/**
  * Axiom of union.
  *
  * For every family F there exists a set U containing all elements of F.
  */
trait ZFUnion {
  def union: ∀[[F] => ∃[[u] => ∀[[y] => ∀[[x] => ((x ∈ y) ∧ (y ∈ F)) => x ∈ u]]]]
}
