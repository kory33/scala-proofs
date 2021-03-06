package com.github.kory33.proof.set.axiom.zf

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.Equality._
import com.github.kory33.proof.set._
import com.github.kory33.proof.set.SetDefinitions._

/**
  * Schema of separation.
  *
  * For every binary predicate F of one free variable and every set x,
  * there exists set y = { u ∈ x | F(u) }.
  *
  * @tparam F unary predicate
  */
trait ZFSeparation {
  def separation[F[_ <: Σ]]: ∀[[x <: Σ] => ∃[[y <: Σ] => ∀[[u <: Σ] => (u ∈ y) <=> ((u ∈ x) ∧ F[u])]]]
}
