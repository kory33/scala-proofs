package com.github.kory33.proof.set.axiom.zf

import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.Equality._
import com.github.kory33.proof.set._
import com.github.kory33.proof.set.SetDefinitions._

/**
  * Axiom of existence.
  *
  * There exists a set.
  */
trait ZFExistence {
  def existence: ∃[[x <: Σ] => x =::= x]
}
