package com.github.kory33.proof.set.logic

import com.github.kory33.proof.logic.predicate.PredicateLogicSystem
import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions.{∃, ∀}
import com.github.kory33.proof.set.AxiomaticSet

object SpecializedPredicateSystem {

  /**
    * Existential generalization
    */
  implicit def genExist[F[_ <: AxiomaticSet], A <: AxiomaticSet](instance: F[A]): ∃[F] = PredicateLogicSystem.genExist[AxiomaticSet, F, A](instance)

  def instUniv[φ[_ <: AxiomaticSet], X <: AxiomaticSet](forall: ∀[φ]): φ[X] = PredicateLogicSystem.instUniv[AxiomaticSet, φ, X](forall)

  /**
    * Existential instantiation(elimination)
    */
  def instExist[F[_ <: AxiomaticSet], φ](exists: ∃[F], forall: ∀[[X <: AxiomaticSet] => F[X] => φ]): φ = PredicateLogicSystem.instExist[AxiomaticSet, F, φ](exists, forall)

  /**
    * Universal generalization
    */
  def genUniv[φ](theorem: φ): ∀[[x <: AxiomaticSet] => φ] = {
    byContradiction { existsNot: ∃[[x <: AxiomaticSet] => ￢[φ]] =>
      theorem ∧ existsNot.value
    }
  }

  def forType[T <: AxiomaticSet] = PredicateLogicSystem.forType[T, AxiomaticSet]

  def notForall[φ[_ <: AxiomaticSet]](notForall: ￢[∀[[x <: AxiomaticSet] => φ[x]]]): ∃[[x <: AxiomaticSet] => ￢[φ[x]]] = PredicateLogicSystem.notForall[AxiomaticSet, φ](notForall)

  /**
    * ∃x.∃y.F(x, y) ⇔ ∃y.∃x.F(x, y)
    */
  def existsCommute[F[_ <: AxiomaticSet, _ <: AxiomaticSet]]: ∃[[x <: AxiomaticSet] => ∃[[y <: AxiomaticSet] => F[x, y]]] <=> ∃[[y <: AxiomaticSet] => ∃[[x <: AxiomaticSet] => F[x, y]]] = PredicateLogicSystem.existsCommute[AxiomaticSet, F]

  /**
    * ∀x.∀y.F(x, y) ⇔ ∀y.∀x.F(x, y)
    */
  def forallCommute[F[_ <: AxiomaticSet, _ <: AxiomaticSet]]: ∀[[x <: AxiomaticSet] => ∀[[y <: AxiomaticSet] => F[x, y]]] <=> ∀[[y <: AxiomaticSet] => ∀[[x <: AxiomaticSet] => F[x, y]]] = PredicateLogicSystem.forallCommute[AxiomaticSet, F]

}