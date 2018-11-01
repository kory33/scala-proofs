package com.github.kory33.experimental.proof.set.axiom.zf

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.experimental.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.experimental.proof.logic.predicate.Equality._
import com.github.kory33.experimental.proof.set._
import com.github.kory33.experimental.proof.set.SetDefinitions._

/**
  * Schema of separation.
  *
  * For every binary predicate F of one free variable and every set x,
  * there exists set y = { u ∈ x | F(u) }.
  *
  * @tparam F unary predicate
  */
trait ZFSeparation {
  def separation[F[_]]: ∀[[x] => ∃[[y] => ∀[[u] => (u ∈ y) <=> ((u ∈ x) ∧ F[u])]]]
}
