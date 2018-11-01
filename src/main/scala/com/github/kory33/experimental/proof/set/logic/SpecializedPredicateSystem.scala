package com.github.kory33.experimental.proof.set.logic

import scala.language.implicitConversions

import com.github.kory33.experimental.proof.logic.predicate.PredicateLogicSystem
import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.experimental.proof.set.logic.SpecializedPredicateDefinitions.{∃, ∀}
import com.github.kory33.experimental.proof.set.logic.SetDomain

object SpecializedPredicateSystem {

  /**
    * Existential generalization
    */
  implicit def genExist[F[_], A : SetDomain](instance: F[A]): ∃[F] = PredicateLogicSystem.genExist[SetDomain, F, A](instance)

  def instUniv[φ[_], X : SetDomain](forall: ∀[φ]): φ[X] = PredicateLogicSystem.instUniv[SetDomain, φ, X](forall)

  implicit def existentialDomain[F[_]](implicit existence: ∃[F]): SetDomain[existence.S] = PredicateLogicSystem.existentialDomain

  /**
    * Existential instantiation(elimination)
    */
  def instExist[F[_], φ](exists: ∃[F], forall: ∀[[X] => F[X] => φ]): φ = PredicateLogicSystem.instExist[SetDomain, F, φ](exists, forall)

  def forType[T : SetDomain] = PredicateLogicSystem.forType[SetDomain, T]
  def forType2[T1 : SetDomain, T2 : SetDomain] = PredicateLogicSystem.forType2[SetDomain, T1, T2]

  def notForall[φ[_]](notForall: ￢[∀[[x] => φ[x]]]): ∃[[x] => ￢[φ[x]]] = PredicateLogicSystem.notForall[SetDomain, φ](notForall)
  def notForall2[φ[_, _]](notForall: ￢[∀[[x] => ∀[[y] => φ[x, y]]]]): ∃[[x] => ∃[[y] => ￢[φ[x, y]]]] = {
    PredicateLogicSystem.notForall2[SetDomain, φ](notForall)
  }
  def notForall3[φ[_, _, _]](notForall: ￢[∀[[x] => ∀[[y] => ∀[[z] => φ[x, y, z]]]]])
    : ∃[[x] => ∃[[y] => ∃[[z] => ￢[φ[x, y, z]]]]] = {
    PredicateLogicSystem.notForall3[SetDomain, φ](notForall)
  }
  def notForall4[φ[_, _, _, _]](notForall: ￢[∀[[x] => ∀[[y] => ∀[[z] => ∀[[w] => φ[x, y, z, w]]]]]])
    : ∃[[x] => ∃[[y] => ∃[[z] => ∃[[w] => ￢[φ[x, y, z, w]]]]]] = {
    PredicateLogicSystem.notForall4[SetDomain, φ](notForall)
  }

  /**
    * ∃x.∃y.F(x, y) ⇔ ∃y.∃x.F(x, y)
    */
  def existsCommute[F[_, _]]: ∃[[x] => ∃[[y] => F[x, y]]] <=> ∃[[y] => ∃[[x] => F[x, y]]] = PredicateLogicSystem.existsCommute[SetDomain, F]

  /**
    * ∀x.∀y.F(x, y) ⇔ ∀y.∀x.F(x, y)
    */
  def forallCommute[F[_, _]]: ∀[[x] => ∀[[y] => F[x, y]]] <=> ∀[[y] => ∀[[x] => F[x, y]]] = PredicateLogicSystem.forallCommute[SetDomain, F]

}