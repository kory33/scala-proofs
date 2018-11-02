package com.github.kory33.proof.set.axiom.zf

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.logic.predicate.Equality._
import com.github.kory33.proof.set._
import com.github.kory33.proof.set.SetDefinitions._

/**
  * Axiom of power set.
  *
  * For every set x there exists a set P containing all subsets of x.
  */
trait ZFPower {
  def power: ∀[[x] => ∃[[p] => ∀[[z] => (z ⊂ x) => (z ∈ p)]]]
}
