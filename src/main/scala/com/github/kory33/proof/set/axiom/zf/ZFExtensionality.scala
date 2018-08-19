package com.github.kory33.proof.set.axiom.zf

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.Equality._
import com.github.kory33.proof.set._
import com.github.kory33.proof.set.SetDefinitions._

/**
  * Axiom of extensionality.
  *
  * For all set x and y, x contains and is contained in y when they have exactly same elements.
  */
trait ZFExtensionality {
  def extensionality: ∀[[x <: Σ] => ∀[[y <: Σ] => ∀[[z <: Σ] => (z ∈ x) <=> (z ∈ y)] => (x =::= y)]]
}
