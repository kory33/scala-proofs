package com.github.kory33.proof.set

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.set.foundation.SetTheoryLanguage

trait BasicPredicates {
  val language: SetTheoryLanguage; import language._

  type ∃![F[_]] = ∃[F] ∧ ∀[[x] => ∀[[y] => (F[x] ∧ F[y]) => x =::= y]]
  type ∀∈[A, F[_]] = ∀[[x] => (x ∈ A) => F[x]]
  type ∃∈[A, F[_]] = ∃[[x] => (x ∈ A) ∧ F[x]]

  type ⊂[x, X] = ∀[[z] => (z ∈ x) => (z ∈ X)]

  type disjoint[x, y] = ￢[∃[[z] => (z ∈ x) ∧ (z ∈ x)]]
  type isEmpty[x] = ￢[∃[[y] => y ∈ x]]
  type hasNonemptySets[F] = ∀∈[F, [x] => ∃[[z] => z ∈ x]]
  type hasDisjointSets[F] = ∀∈[F, [x] => ∀∈[F, [y] => (x =::= y) ∨ disjoint[x, y]]]
  type isSingletonOf[s, x] = ∀∈[s, [y] => y =::= x]
  type isSucc[s, x] = ∀∈[s, [y] => (y =::= x) ∨ (y isSingletonOf x)]
  
}
