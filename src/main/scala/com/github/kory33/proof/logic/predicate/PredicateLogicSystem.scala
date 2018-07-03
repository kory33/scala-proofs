package com.github.kory33.proof.logic.predicate

import com.github.kory33.proof.logic.predicate.PredicateLogicDefinitions.{∀, ∃}
import com.github.kory33.proof.logic.propositional.ClassicalLogicAxiom
import com.github.kory33.proof.logic.propositional.LogicDefinitions.{￢, _}
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.logic.propositional.ClassicalLogicSystem._

object PredicateLogicSystem {

  /**
    * Existential generalization
    */
  implicit def genExist[F[_], A](instance: F[A]): ∃[F] = new ∃ { type S = A; def value = instance }

  /**
    * Existential instantiation(elimination)
    */
  def instExist[F[_], φ](exists: ∃[F], forall: ∀[[X] => F[X] => φ])(implicit axiom: PredicateLogicAxiom): φ = {
    axiom.instUniv[[x] => F[x] => φ, exists.S](forall)(exists.value)
  }

  def notForall[φ[_]](notForall: ￢[∀[[x] => φ[x]]])(implicit classicalLogicAxiom: ClassicalLogicAxiom): ∃[[x] => ￢[φ[x]]] = {
    eliminateDoubleNegation(notForall)
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
  def forallCommute[F[_, _]](implicit
                             predicateLogicAxiom: PredicateLogicAxiom,
                             classicalLogicAxiom: ClassicalLogicAxiom): ∀[[x] => ∀[[y] => F[x, y]]] ≣ ∀[[y] => ∀[[x] => F[x, y]]] = {
    val implies = eliminateDoubleNegation(
      byContradiction { negation: ￢[∀[[x] => ∀[[y] => F[x, y]]] => ∀[[y] => ∀[[x] => F[x, y]]]] =>
        val ev1 = nonImplication.implies(negation)
        val ev2: ∀[[x] => ∀[[y] => F[x, y]]] = ev1._1
        val ev3: ￢[∀[[y] => ∀[[x] => F[x, y]]]] = ev1._2
        val ev4: ∃[[y] => ￢[∀[[x] => F[x, y]]]] = notForall[[y] => ∀[[x] => F[x, y]]](ev3)
        type Y = ev4.S
        val ev5: ￢[∀[[x] => F[x, Y]]] = ev4.value
        val ev6: ∃[[x] => ￢[F[x, Y]]] = notForall[[x] => F[x, Y]](ev5)
        type X = ev6.S
        val ev7: ￢[F[X, Y]] = ev6.value
        val ev8: F[X, Y] = predicateLogicAxiom.instUniv[[y] => F[X, y], Y](
          predicateLogicAxiom.instUniv[[x] => ∀[[y] => F[x, y]], X](ev2)
        )
        ev8 ∧ ev7
      }
    )

    val impliedBy = eliminateDoubleNegation(
      byContradiction { negation: ￢[∀[[y] => ∀[[x] => F[x, y]]] => ∀[[x] => ∀[[y] => F[x, y]]]] =>
        val ev1 = nonImplication.implies(negation)
        val ev2: ∀[[y] => ∀[[x] => F[x, y]]] = ev1._1
        val ev3: ￢[∀[[x] => ∀[[y] => F[x, y]]]] = ev1._2
        val ev4: ∃[[x] => ￢[∀[[y] => F[x, y]]]] = notForall[[x] => ∀[[y] => F[x, y]]](ev3)
        type X = ev4.S
        val ev5: ￢[∀[[y] => F[X, y]]] = ev4.value
        val ev6: ∃[[y] => ￢[F[X, y]]] = notForall[[y] => F[X, y]](ev5)
        type Y = ev6.S
        val ev7: ￢[F[X, Y]] = ev6.value
        val ev8: F[X, Y] = predicateLogicAxiom.instUniv[[x] => F[x, Y], X](
          predicateLogicAxiom.instUniv[[y] => ∀[[x] => F[x, y]], Y](ev2)
        )
        ev8 ∧ ev7
      }
    )

    implies ∧ impliedBy
  }

}
