package com.github.kory33.proof.set

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.predicate.PredicateLogicDefinitions._

object SetDefinitions {

  type ∈[x, y]
  type =#=[x, y]

  type ∉[x, y] = ￢[x ∈ y]
  type =/=[x, y] = ￢[x =#= y]
  type ⊂[x, y] = ∀[[z] => (z ∈ x) => (z ∈ y)]
  type ⊃[x, y] = y ⊂ x

  /**
   * x = ∅
   */
  type isEmpty[x] = ∀[[y] => y ∉ x]

  /**
   * x ≠ ∅
   */
  type isNonEmpty[x] = ∃[[y] => y ∈ x]

  /**
   * y = Succ(x) where Succ(x) = x ∪ {x}
   */
  type isSucc[y, x] = ∀[[z] => (z ∈ y) ≣ (z ∈ x ∨ z =#= x)]

  type hasAll[A, F[_]] = ∀[[x] => (x ∈ A) => F[x]]
  type hasSome[A, F[_]] = ∃[[x] => (x ∈ A) ∧ F[x]]

  /**
   * Unique existence
   */
  type ∃![F[_]] = ∃[F] ∧ ∀[[x] => ∀[[y] => (F[x] ∧ F[y]) => x =#= y]]

  /**
   * x and y are disjoint
   */
  type isDisjointTo[x, y] = ￢[∃[[z] => (z ∈ x) ∧ (z ∈ y)]]

  /**
   * F is a pairwise disjoint family
   */
  type isPairwiseDisjoint[F] = F hasAll ([x] => F hasAll ([y] => (x =#= y) ∨ (x isDisjointTo y)))

  /**
   * S is a selector of F that intersects every x ∈ F in precisely one point
   */
  type isASelectorOn[S, F] = F hasAll ([x] => ∃![[z] => (z ∈ S) ∧ z ∈ x])

  /**
   * y = {x}
   */
  type containsJust[y, x] = ∀[[z] => z ∈ y ≣ z =#= x]

}
