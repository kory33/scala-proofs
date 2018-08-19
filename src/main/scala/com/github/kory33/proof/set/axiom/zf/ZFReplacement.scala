package com.github.kory33.proof.set.axiom.zf

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.Equality._
import com.github.kory33.proof.set._
import com.github.kory33.proof.set.SetDefinitions._

/**
  * Axiom schema of replacement.
  *
  * For every formula φ, A and p, if φ(s, t, A, p) defines a function F on A by F(x) = y ⇔ φ(x, y, A, p)
  * then there exists a set Y containing the range F[A] = {F(x): x ∈ A} of the function F.
  */
trait ZFReplacement {
  def replacement[φ[_ <: Σ, _ <: Σ, _ <: Σ, _ <: Σ]]: ∀[[A <: Σ] => ∀[[p <: Σ] => A hasAll ([x <: Σ] => ∃![[y <: Σ] => φ[x, y, A, p]]) => ∃[[Y <: Σ] => A hasAll ([x <: Σ] => Y hasSome ([y <: Σ] => φ[x, y, A, p]))]]]
}
