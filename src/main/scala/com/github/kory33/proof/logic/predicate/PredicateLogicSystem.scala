package com.github.kory33.proof.logic.predicate

import com.github.kory33.proof.logic.predicate.PredicateLogicDefinitions.{∀, ∃}
import com.github.kory33.proof.logic.propositional.ClassicalLogicAxiom
import com.github.kory33.proof.logic.propositional.LogicDefinitions.{￢, _}
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._

object PredicateLogicSystem {

  /**
    * Existential generalization
    */
  implicit def genExist[F[_], A](instance: F[A]): ∃[F] = new ∃ { type S = A; def value = instance }

  /**
    * Existential instantiation(elimination)
    */
  def instExist[F[_], φ](exists: ∃[F], forall: ∀[[X] => F[X] => φ])(implicit axiom: PredicateLogicAxiom): φ = {
    axiom.instUniv[[X] => F[X] => φ, exists.S](forall)(exists.value)
  }

  /**
    * ∀x.∀y.F(x, y) ⇔ ∀y.∀x.F(x, y)
    */
  def forallCommute[F[_, _]]: ∀[[x] => ∀[[y] => F[x, y]]] ≣ ∀[[y] => ∀[[x] => F[x, y]]] = ??? // TODO

  /**
    * ∃x.∃y.F(x, y) ⇔ ∃y.∃x.F(x, y)
    */
  def existsCommute[F[_, _]]: ∃[[x] => ∃[[y] => F[x, y]]] ≣ ∃[[y] => ∃[[x] => F[x, y]]] = ??? // TODO

}
