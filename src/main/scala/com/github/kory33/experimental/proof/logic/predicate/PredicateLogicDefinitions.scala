package com.github.kory33.experimental.proof.logic.predicate

import com.github.kory33.proof.logic.propositional.LogicDefinitions.￢

object PredicateLogicDefinitions {

  type Id[x] = x

  /**
   * Existential quantification
   * 
   * typeclass [[D]] represents a domain of discourse, and [[typeclass]] ensures that type [[S]] is an element of [[D]].
   * typeclass [[F]] represents a predicate for which application to type [[S]] becomes truth.
   *
   * overall, the instance of this trait represents ∃S∈D.F[S] (here the relation ∈ is not set-theoretic).
   */
  trait ∃[D[_], F[_]] {
    type S
    val typeclass: D[S]
    val instance: F[S]
  }

  /**
   * Universal quantification
   */
  type ∀[D[_], F[_]] = ￢[∃[D, [x] => ￢[F[x]]]]

  /**
   * There exists a type constructor F such that [[P]] is fulfilled and the constructed type belongs to typeclass [[D]].
   */
  trait ∃~>[D[_], P[_[_]]] {
    type F[_]
    val typeclass: ∀[Id, [x] => D[F[x]]]
    val instance: P[F]
  }

}
