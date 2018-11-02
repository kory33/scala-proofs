package com.github.kory33.proof.set.axiom.zf

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.logic.predicate.Equality._
import com.github.kory33.proof.set._
import com.github.kory33.proof.set.SetDefinitions._

/**
  * Axiom of Infinity.
  *
  * There exists an infinite set of some special form.
  */
trait ZFInfinity {
  def infinity: ∃[[x] => ∀[[z] => isEmpty[z] => (z ∈ x)] ∧ (x hasAll ([y] => ∀[[z] => (z isSucc y) => (z ∈ x)]))]
}
