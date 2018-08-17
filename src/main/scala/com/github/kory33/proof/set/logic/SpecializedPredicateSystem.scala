package com.github.kory33.proof.set.logic

import scala.language.implicitConversions

import com.github.kory33.proof.logic.predicate.PredicateLogicSystem
import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions.{∃, ∀}
import com.github.kory33.proof.set.Σ

object SpecializedPredicateSystem {

  /**
    * Existential generalization
    */
  implicit def genExist[F[_ <: Σ], A <: Σ](instance: F[A]): ∃[F] = PredicateLogicSystem.genExist[Σ, F, A](instance)

  def instUniv[φ[_ <: Σ], X <: Σ](forall: ∀[φ]): φ[X] = PredicateLogicSystem.instUniv[Σ, φ, X](forall)

  /**
    * Existential instantiation(elimination)
    */
  def instExist[F[_ <: Σ], φ](exists: ∃[F], forall: ∀[[X <: Σ] => F[X] => φ]): φ = PredicateLogicSystem.instExist[Σ, F, φ](exists, forall)

  /**
    * Universal generalization
    */
  def genUniv[φ](theorem: φ): ∀[[x <: Σ] => φ] = {
    byContradiction { existsNot: ∃[[x <: Σ] => ￢[φ]] =>
      theorem ∧ existsNot.value
    }
  }

  def forType[T <: Σ] = PredicateLogicSystem.forType[T, Σ]

  def notForall[φ[_ <: Σ]](notForall: ￢[∀[[x <: Σ] => φ[x]]]): ∃[[x <: Σ] => ￢[φ[x]]] = PredicateLogicSystem.notForall[Σ, φ](notForall)

  /**
    * ∃x.∃y.F(x, y) ⇔ ∃y.∃x.F(x, y)
    */
  def existsCommute[F[_ <: Σ, _ <: Σ]]: ∃[[x <: Σ] => ∃[[y <: Σ] => F[x, y]]] <=> ∃[[y <: Σ] => ∃[[x <: Σ] => F[x, y]]] = PredicateLogicSystem.existsCommute[Σ, F]

  /**
    * ∀x.∀y.F(x, y) ⇔ ∀y.∀x.F(x, y)
    */
  def forallCommute[F[_ <: Σ, _ <: Σ]]: ∀[[x <: Σ] => ∀[[y <: Σ] => F[x, y]]] <=> ∀[[y <: Σ] => ∀[[x <: Σ] => F[x, y]]] = PredicateLogicSystem.forallCommute[Σ, F]

}