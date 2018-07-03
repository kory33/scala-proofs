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
    def implies[G[_, _]]: ∃[[x] => ∃[[y] => G[x, y]]] => ∃[[w] => ∃[[z] => G[z, w]]] = { exists =>
      type X = exists.S
      val ev1: ∃[[y] => G[X, y]] = exists.value

      type Y = ev1.S
      val ev2: G[X, Y] = ev1.value

      val ev3: ∃[[x] => G[x, Y]] = genExist[[x] => G[x, Y], X](ev2)
      genExist[[y] => ∃[[x] => G[x, y]], Y](ev3)
    }

    implies[F] ∧ implies[[X, Y] => F[Y, X]]
  }

  /**
    * ∀x.∀y.F(x, y) ⇔ ∀y.∀x.F(x, y)
    */
  def forallCommute[F[_, _]](implicit
                             predicateLogicAxiom: PredicateLogicAxiom,
                             classicalLogicAxiom: ClassicalLogicAxiom): ∀[[x] => ∀[[y] => F[x, y]]] ≣ ∀[[y] => ∀[[x] => F[x, y]]] = {
    def implies[G[_, _]] = eliminateDoubleNegation(
      byContradiction { negation: ￢[∀[[x] => ∀[[y] => G[x, y]]] => ∀[[y] => ∀[[x] => G[x, y]]]] =>
        val ev1 = nonImplication.implies(negation)
        val ev2: ∀[[x] => ∀[[y] => G[x, y]]] = ev1._1
        val ev3: ￢[∀[[y] => ∀[[x] => G[x, y]]]] = ev1._2
        val ev4: ∃[[y] => ￢[∀[[x] => G[x, y]]]] = notForall[[y] => ∀[[x] => G[x, y]]](ev3)
        type Y = ev4.S
        val ev5: ￢[∀[[x] => G[x, Y]]] = ev4.value
        val ev6: ∃[[x] => ￢[G[x, Y]]] = notForall[[x] => G[x, Y]](ev5)
        type X = ev6.S
        val ev7: ￢[G[X, Y]] = ev6.value
        val ev8: G[X, Y] = predicateLogicAxiom.instUniv[[y] => G[X, y], Y](
          predicateLogicAxiom.instUniv[[x] => ∀[[y] => G[x, y]], X](ev2)
        )
        ev8 ∧ ev7
      }
    )

    implies[F] ∧ implies[[X, Y] => F[Y, X]]
  }

}
