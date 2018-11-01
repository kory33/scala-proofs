package com.github.kory33.experimental.proof.set.axiom.zf

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.experimental.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.experimental.proof.logic.predicate.Equality._
import com.github.kory33.experimental.proof.set._
import com.github.kory33.experimental.proof.set.SetDefinitions._

/**
  * Axiom of foundation / regularity.
  * Every nonempty set has an ∈-minimal element.
  */
trait ZFFoundation {
  def foundation: ∀[[x] => isNonEmpty[x] => x hasSome ([y] => x isDisjointTo y)]
}
