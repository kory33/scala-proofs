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
    * ∃x.∃y.F(x, y) ⇔ ∃y.∃x.F(x, y)
    */
  def existsCommute[F[_, _]]: ∃[[x] => ∃[[y] => F[x, y]]] ≣ ∃[[y] => ∃[[x] => F[x, y]]] = {
    val implies: ∃[[x] => ∃[[y] => F[x, y]]] => ∃[[w] => ∃[[z] => F[z, w]]] = { exists =>
      type X = exists.S
      val ev1: ∃[[y] => F[X, y]] = exists.value

      type Y = ev1.S
      val ev2: F[X, Y] = ev1.value

      val ev3: ∃[[x] => F[x, Y]] = genExist[[x] => F[x, Y], X](ev2)
      genExist[[y] => ∃[[x] => F[x, y]], Y](ev3)
    }

    val impliedBy: ∃[[y] => ∃[[x] => F[x, y]]] => ∃[[x] => ∃[[y] => F[x, y]]] = { exists =>
      type Y = exists.S
      val ev1: ∃[[x] => F[x, Y]] = exists.value

      type X = ev1.S
      val ev2: F[X, Y] = ev1.value

      val ev3: ∃[[y] => F[X, y]] = genExist[[y] => F[X, y], Y](ev2)
      genExist[[x] => ∃[[y] => F[x, y]], X](ev3)
    }

    implies ∧ impliedBy
  }

  /**
    * ∀x.∀y.F(x, y) ⇔ ∀y.∀x.F(x, y)
    */
  def forallCommute[F[_, _]]: ∀[[x] => ∀[[y] => F[x, y]]] ≣ ∀[[y] => ∀[[x] => F[x, y]]] = ???

}
