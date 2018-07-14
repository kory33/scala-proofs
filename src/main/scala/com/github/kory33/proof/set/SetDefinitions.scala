package com.github.kory33.proof.set

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._

class AxiomaticSet

object SetDefinitions {

  type ∈[x <: AxiomaticSet, y <: AxiomaticSet]
  type =#=[x <: AxiomaticSet, y <: AxiomaticSet]

  type ∉[x <: AxiomaticSet, y <: AxiomaticSet] = ￢[x ∈ y]
  type =/=[x <: AxiomaticSet, y <: AxiomaticSet] = ￢[x =#= y]
  type ⊂[x <: AxiomaticSet, y <: AxiomaticSet] = ∀[[z <: AxiomaticSet] => (z ∈ x) => (z ∈ y)]
  type ⊃[x <: AxiomaticSet, y <: AxiomaticSet] = y ⊂ x

  /**
   * x = ∅
   */
  type isEmpty[x <: AxiomaticSet] = ∀[[y <: AxiomaticSet] => y ∉ x]

  /**
   * x ≠ ∅
   */
  type isNonEmpty[x <: AxiomaticSet] = ∃[[y <: AxiomaticSet] => y ∈ x]

  /**
   * y = Succ(x) where Succ(x) = x ∪ {x}
   */
  type isSucc[y <: AxiomaticSet, x <: AxiomaticSet] = ∀[[z <: AxiomaticSet] => (z ∈ y) <=> ((z ∈ x) ∨ (z =#= x))]

  type hasAll[A <: AxiomaticSet, F[_ <: AxiomaticSet]] = ∀[[x <: AxiomaticSet] => (x ∈ A) => F[x]]
  type hasSome[A <: AxiomaticSet, F[_ <: AxiomaticSet]] = ∃[[x <: AxiomaticSet] => (x ∈ A) ∧ F[x]]

  /**
   * Unique existence
   */
  type ∃![F[_ <: AxiomaticSet]] = ∃[F] ∧ ∀[[x <: AxiomaticSet] => ∀[[y <: AxiomaticSet] => (F[x] ∧ F[y]) => x =#= y]]

  /**
   * x and y are disjoint
   */
  type isDisjointTo[x <: AxiomaticSet, y <: AxiomaticSet] = ￢[∃[[z <: AxiomaticSet] => (z ∈ x) ∧ (z ∈ y)]]

  /**
   * F is a pairwise disjoint family
   */
  type isPairwiseDisjoint[F <: AxiomaticSet] = F hasAll ([x <: AxiomaticSet] => F hasAll ([y <: AxiomaticSet] => (x =#= y) ∨ (x isDisjointTo y)))

  /**
   * S is a selector of F that intersects every x ∈ F in precisely one point
   */
  type isASelectorOn[S <: AxiomaticSet, F <: AxiomaticSet] = F hasAll ([x <: AxiomaticSet] => ∃![[z <: AxiomaticSet] => (z ∈ S) ∧ (z ∈ x)])

  /**
   * z = {x, y}
   */
  type isPairOfJust[z <: AxiomaticSet, x <: AxiomaticSet, y <: AxiomaticSet] = ∀[[w <: AxiomaticSet] => (w ∈ z) <=> ((w =#= x) ∨ (w =#= y))]

  /**
   * y = {x}
   */
  type containsJust[y <: AxiomaticSet, x <: AxiomaticSet] = ∀[[z <: AxiomaticSet] => (z ∈ y) <=> (z =#= x)]

}
