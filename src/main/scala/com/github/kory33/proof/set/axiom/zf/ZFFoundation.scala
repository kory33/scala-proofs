package com.github.kory33.proof.set.axiom.zf

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.Equality._
import com.github.kory33.proof.set._
import com.github.kory33.proof.set.SetDefinitions._

/**
  * Axiom of foundation / regularity.
  * Every nonempty set has an ∈-minimal element.
  */
trait ZFFoundation {
  def foundation: ∀[[x <: Σ] => isNonEmpty[x] => x hasSome ([y <: Σ] => x isDisjointTo y)]
}
