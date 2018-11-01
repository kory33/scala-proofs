package com.github.kory33.experimental.proof.set.axiom.zf

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.experimental.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.experimental.proof.logic.predicate.Equality._
import com.github.kory33.experimental.proof.set._
import com.github.kory33.experimental.proof.set.SetDefinitions._

/**
  * Axiom of extensionality.
  *
  * For all set x and y, x contains and is contained in y when they have exactly same elements.
  */
trait ZFExtensionality {
  def extensionality: ∀[[x] => ∀[[y] => ∀[[z] => (z ∈ x) <=> (z ∈ y)] => (x =::= y)]]
}
