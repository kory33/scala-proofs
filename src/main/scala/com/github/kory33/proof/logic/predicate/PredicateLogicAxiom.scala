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

}
