package com.github.kory33.proof.set.peano

import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateSystem._
import com.github.kory33.proof.set.logic._
import com.github.kory33.proof.set.logic.Equality._
import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set._

trait Peano[X <: Σ, x <: Σ, f[_ <: Σ] <: Σ] {
  
  def zero: ￢[∃[[y <: Σ] => f[y] =::= x]]

  def injection: isInjective[f]

  def inductive: ∀[[A <: Σ] => (A ⊂ X) => (x ∈ A) ∧ ∀[[a <: Σ] => a ∈ A => f[a] ∈ A] => A =::= X]

}
