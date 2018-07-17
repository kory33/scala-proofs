package com.github.kory33.proof.set

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._

class Σ

object SetDefinitions {

  type ∈[x <: Σ, y <: Σ]
  type =#=[x <: Σ, y <: Σ]

  type ∉[x <: Σ, y <: Σ] = ￢[x ∈ y]
  type =/=[x <: Σ, y <: Σ] = ￢[x =#= y]
  type ⊂[x <: Σ, y <: Σ] = ∀[[z <: Σ] => (z ∈ x) => (z ∈ y)]
  type ⊃[x <: Σ, y <: Σ] = y ⊂ x

  /**
   * x = ∅
   */
  type isEmpty[x <: Σ] = ∀[[y <: Σ] => y ∉ x]

  /**
   * x ≠ ∅
   */
  type isNonEmpty[x <: Σ] = ∃[[y <: Σ] => y ∈ x]

  /**
   * y = Succ(x) where Succ(x) = x ∪ {x}
   */
  type isSucc[y <: Σ, x <: Σ] = ∀[[z <: Σ] => (z ∈ y) <=> ((z ∈ x) ∨ (z =#= x))]

  type hasAll[A <: Σ, F[_ <: Σ]] = ∀[[x <: Σ] => (x ∈ A) => F[x]]
  type hasSome[A <: Σ, F[_ <: Σ]] = ∃[[x <: Σ] => (x ∈ A) ∧ F[x]]

  /**
   * Unique existence
   */
  type ∃![F[_ <: Σ]] = ∃[F] ∧ ∀[[x <: Σ] => ∀[[y <: Σ] => (F[x] ∧ F[y]) => x =#= y]]

  /**
   * x and y are disjoint
   */
  type isDisjointTo[x <: Σ, y <: Σ] = ￢[∃[[z <: Σ] => (z ∈ x) ∧ (z ∈ y)]]

  /**
   * F is a pairwise disjoint family
   */
  type isPairwiseDisjoint[F <: Σ] = F hasAll ([x <: Σ] => F hasAll ([y <: Σ] => (x =#= y) ∨ (x isDisjointTo y)))

  /**
   * S is a selector of F that intersects every x ∈ F in precisely one point
   */
  type isASelectorOn[S <: Σ, F <: Σ] = F hasAll ([x <: Σ] => ∃![[z <: Σ] => (z ∈ S) ∧ (z ∈ x)])

  /**
   * z = {x, y}
   */
  type isPairOfJust[z <: Σ, x <: Σ, y <: Σ] = ∀[[w <: Σ] => (w ∈ z) <=> ((w =#= x) ∨ (w =#= y))]

  /**
   * y = {x}
   */
  type containsJust[y <: Σ, x <: Σ] = ∀[[z <: Σ] => (z ∈ y) <=> (z =#= x)]

  /**
   * y is a power set of x.
   */
  type isPowerOf[y <: Σ, x <: Σ] = ∀[[z <: Σ] => (z ∈ y) <=> (z ⊂ x)]

}
