package com.github.kory33.proof.set.axiom.zf

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.logic.predicate.Equality._
import com.github.kory33.proof.set._
import com.github.kory33.proof.set.SetDefinitions._

/**
  * Axiom of pairing
  *
  * For any a and b there exists x that contains a and b.
  */
trait ZFParing {
  def pairing: ∀[[a] => ∀[[b] => ∃[[x] => ∀[[w] => ((w =::= a) ∨ (w =::= b)) => (w ∈ x)]]]]
}
