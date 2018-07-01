package com.github.kory33.proof.logic.predicate

import com.github.kory33.proof.logic.predicate.PredicateLogicDefinitions.{∀, ∃}
import com.github.kory33.proof.logic.propositional.ClassicalLogicAxiom
import com.github.kory33.proof.logic.propositional.LogicDefinitions.{￢, _}
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._

object PredicateLogicSystem {

  /**
    * Existential generalization
    */
  implicit def genExist[F[_], A](instance: F[A]): ∃[F] = instance.asInstanceOf[F[_]]

/*
  /**
    * Existential instantiation(elimination)
    */
  def instExist[F[_], φ](exists: ∃[F], forall: ∀[[X] => F[X] => φ])(implicit axiom: PredicateLogicAxiom): φ = {
    axiom.instUniv[[X] => F[X] => φ](forall)
  }

  /*
  /**
    * ∀x.∀y.F(x, y) ⇔ ∀y.∀x.F(x, y)
    */
  def forallCommute[F[_, _]]: ∀[[x] => ∀[[y] => F[x, y]]] ≣ ∀[[y] => ∀[[x] => F[x, y]]] = {

    val implies:
      ∀[({type λ1[x] = ∀[({ type λ2[y] = F[x, y] })#λ2] })#λ1] =>
        ∀[({type λ1[y] = ∀[({ type λ2[x] = F[x, y] })#λ2] })#λ1] = identity

    val impliedBy:
      ∀[({type λ1[y] = ∀[({ type λ2[x] = F[x, y] })#λ2] })#λ1] =>
        ∀[({type λ1[x] = ∀[({ type λ2[y] = F[x, y] })#λ2] })#λ1] = identity

    implies ∧ impliedBy

  }

  /**
    * ∃x.∃y.F(x, y) ⇔ ∃y.∃x.F(x, y)
    */
  def existsCommute[F[_, _]]: ∃[[x] => ∃[[y] => F[x, y]]] ≣ ∃[[y] => ∃[[x] => F[x, y]]] = {

  }

  */
}
