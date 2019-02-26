package com.github.kory33.proof.set

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.set.foundation.SetTheoryLanguage

trait BasicPredicates {
  val language: SetTheoryLanguage; import language._

  type Unique[F[_]] = ∀[[x] => ∀[[y] => (F[x] ∧ F[y]) => x =::= y]]
  type ∃![F[_]] = ∃[F] ∧ Unique[F]
  type ∀∈[A, F[_]] = ∀[[x] => (x ∈ A) => F[x]]
  type ∃∈[A, F[_]] = ∃[[x] => (x ∈ A) ∧ F[x]]

  type ⊂[x, X] = ∀[[z] => (z ∈ x) => (z ∈ X)]

  type isEmpty[x] = ∀[[y] => ￢[y ∈ x]]
  type containsTwo[z, x, y] = ∀[[w] => (w ∈ z) <=> ((w =::= x) ∨ (w =::= y))]
  type isUnionOf[U, F] = ∀[[x] => (x ∈ U) <=> ∃[[Y] => ((x ∈ Y) ∧ (Y ∈ F))]]
  type isPowerOf[y, x] = ∀[[z] => (z ∈ y) <=> (z ⊂ x)]
  type isSelectorOn[S, F] = ∀∈[F, [x] => ∃![[z] => (z ∈ S) ∧ (z ∈ x)]]

  type isSingletonOf[s, x] = ∀∈[s, [y] => y =::= x]
  type isSucc[s, x] = ∀∈[s, [y] => (y =::= x) ∨ (y isSingletonOf x)]

  type disjoint[x, y] = ￢[∃[[z] => (z ∈ x) ∧ (z ∈ x)]]
  type hasNonemptySets[F] = ∀∈[F, [x] => ∃[[z] => z ∈ x]]
  type hasDisjointSets[F] = ∀∈[F, [x] => ∀∈[F, [y] => (x =::= y) ∨ disjoint[x, y]]]

  type isSumOf[z, x, y] = ∀[[w] => (w ∈ z) <=> (w ∈ x) ∨ (w ∈ y)]
  type isIntersectionOf[z, x, y] = ∀[[w] => (w ∈ z) <=> (w ∈ x) ∧ (w ∈ y)]

  type isInjective[f[_]] = ∀[[x] => ∀[[y] => (f[x] =::= f[y]) => (x =::= y)]]
  
}