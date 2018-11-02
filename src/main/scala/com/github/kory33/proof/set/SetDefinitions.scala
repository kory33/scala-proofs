package com.github.kory33.proof.set

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.predicate.Equality._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic._

object SetDefinitions {

  class ∈[x, y](implicit val xSetDomain: SetDomain[x], implicit val ySetDomain: SetDomain[y])

  type ∉[x, y] = ￢[x ∈ y]
  type =/=[x, y] = ￢[x =::= y]
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
  type isSucc[y, x] = ∀[[z] => (z ∈ y) <=> ((z ∈ x) ∨ (z =::= x))]

  type hasAll[A, F[_]] = ∀[[x] => (x ∈ A) => F[x]]
  type hasSome[A, F[_]] = ∃[[x] => (x ∈ A) ∧ F[x]]

  type isRangeOfClassFn[FA, F[_], A] = ∀[[z] => (z ∈ FA) <=> (A hasSome ([a] => z =::= F[a]))]

  /**
   * If there are two types satisfying F, they are equal.
   */
  type Unique[F[_]] = ∀[[x] => ∀[[y] => (F[x] ∧ F[y]) => x =::= y]]

  /**
   * Unique existence
   */
  type ∃![F[_]] = ∃[F] ∧ Unique[F]

  /**
   * x and y are disjoint
   */
  type isDisjointTo[x, y] = ￢[∃[[z] => (z ∈ x) ∧ (z ∈ y)]]

  /**
   * F is a pairwise disjoint family
   */
  type isPairwiseDisjoint[F] = F hasAll ([x] => F hasAll ([y] => (x =::= y) ∨ (x isDisjointTo y)))

  /**
   * S is a selector of F that intersects every x ∈ F in precisely one point
   */
  type isASelectorOn[S, F] = F hasAll ([x] => ∃![[z] => (z ∈ S) ∧ (z ∈ x)])

  /**
   * z = {x, y}
   */
  type containsTwo[z, x, y] = ∀[[w] => (w ∈ z) <=> ((w =::= x) ∨ (w =::= y))]

  /**
   * y = {x}
   */
  type isSingletonOf[y, x] = ∀[[z] => (z ∈ y) <=> (z =::= x)]

  /**
   * U = Union of family F
   */
  type isUnionOf[U, F] = ∀[[x] => (x ∈ U) <=> ∃[[Y] => ((x ∈ Y) ∧ (Y ∈ F))]]

  /**
   * y is a power set of x.
   */
  type isPowerOf[y, x] = ∀[[z] => (z ∈ y) <=> (z ⊂ x)]

  /**
   * z is a sum of x and y.
   */
  type isSumOf[z, x, y] = ∀[[w] => (w ∈ z) <=> (w ∈ x) ∨ (w ∈ y)]

  type isIntersectionOf[z, x, y] = ∀[[w] => (w ∈ z) <=> (w ∈ x) ∧ (w ∈ y)]

  /**
   * given class function is injective.
   */
  type isInjective[f[_]] = ∀[[x] => ∀[[y] => (f[x] =::= f[y]) => (x =::= y)]]

}
