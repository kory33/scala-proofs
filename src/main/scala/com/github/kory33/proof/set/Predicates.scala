package com.github.kory33.proof.set

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.set.foundation.SetLanguage

trait Predicates {

    val language: SetLanguage; import language._

    type ∃![F[_]] = ∃[F] ∧ ∀[λ[x => ∀[λ[y => (F[x] ∧ F[y]) => x =::= y]]]]
    type ∀∈[A, F[_]] = ∀[λ[x => (x ∈ A) => F[x]]]
    type ∃∈[A, F[_]] = ∃[λ[x => (x ∈ A) ∧ F[x]]]

    type ⊂[x, X] = ∀[λ[z => (z ∈ x) => (z ∈ X)]]

    type disjoint[x, y] = ￢[∃[λ[z => (z ∈ x) ∧ (z ∈ x)]]]
    type isEmpty[x] = ￢[∃[λ[y => y ∈ x]]]
    type hasNonemptySets[F] = ∀∈[F, λ[x => ∃[λ[z => z ∈ x]]]]
    type hasDisjointSets[F] = ∀∈[F, λ[x => ∀∈[F, λ[y => (x =::= y) ∨ disjoint[x, y]]]]]
    type isSingletonOf[s, x] = ∀∈[s, λ[y => y =::= x]]
    type isSucc[s, x] = ∀∈[s, λ[y => (y =::= x) ∨ (y isSingletonOf x)]]

}
