package com.github.kory33.experimental.proof.set.axiom.zf

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.experimental.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.experimental.proof.logic.predicate.Equality._
import com.github.kory33.experimental.proof.set._
import com.github.kory33.experimental.proof.set.SetDefinitions._

/**
  * Axiom of Infinity.
  *
  * There exists an infinite set of some special form.
  */
trait ZFInfinity {
  def infinity: ∃[[x] => ∀[[z] => isEmpty[z] => (z ∈ x)] ∧ (x hasAll ([y] => ∀[[z] => (z isSucc y) => (z ∈ x)]))]
}
