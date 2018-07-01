package com.github.kory33.proof.logic.predicate

import com.github.kory33.proof.logic.predicate.PredicateLogicDefinitions.{∀, ∃}
import com.github.kory33.proof.logic.propositional.LogicDefinitions.{≣, ￢}

trait PredicateLogicAxiom {

  def axiom1[φ[_], Ψ[_]]: ∀[({ type λ[X] = φ[X] => Ψ[X] })#λ] => ∀[φ] => ∀[Ψ]

  /**
    * Universal instantiation
    *
    * This "constructs" a value of φ[X] given ∀[φ] and any type X.
    */
  def instUniv[φ[_], X]: ∀[φ] => φ[X]

  /**
    * Universal generalization
    *
    * Given a constructor for any type, we can say that for all type there exists φ[A].
    */
  def genUniv[φ[_], X]: (X => φ[X]) => ∀[φ]

}
