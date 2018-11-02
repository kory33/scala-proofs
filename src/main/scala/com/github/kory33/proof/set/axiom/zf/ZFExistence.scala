package com.github.kory33.proof.set.axiom.zf

import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.logic.predicate.Equality._
import com.github.kory33.proof.set.logic._
import com.github.kory33.proof.set.SetDefinitions._

/**
  * Axiom of existence.
  *
  * There exists a set.
  */
trait ZFExistence {
  def existence: ∃[[x] => x =::= x]
}
