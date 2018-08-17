package com.github.kory33.proof.logic.predicate

import scala.language.implicitConversions

import com.github.kory33.proof.logic.predicate.PredicateLogicDefinitions.{∀, ∃}
import com.github.kory33.proof.logic.propositional.LogicDefinitions.{￢, _}
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.logic.propositional.ClassicalLogicSystem._

object PredicateLogicSystem {

  /**
    * Existential generalization
    */
  implicit def genExist[D, F[_ <: D], A <: D](instance: F[A]): ∃[D, F] = new ∃ { type S = A; val value = instance }

  def instUniv[D, φ[_ <: D], X <: D](forall: ∀[D, φ]): φ[X] = {
    byContradiction { notPX: ￢[φ[X]] =>
      val ev11: ∃[D, [x <: D] => ￢[φ[x]]] = notPX
      val ev12: ￢[∃[D, [x <: D] => ￢[φ[x]]]] = forall
      ev11 ∧ ev12
    }
  }

  /**
    * Existential instantiation(elimination)
    */
  def instExist[D, F[_ <: D], φ](exists: ∃[D, F], forall: ∀[D, [X <: D] => F[X] => φ]): φ = {
    val ev1: F[exists.S] => φ = instUniv[D, [x <: D] => F[x] => φ, exists.S](forall)
    ev1(exists.value)
  }

  /**
    * Universal generalization
    */
  def genUniv[φ](theorem: φ): ∀[Any, [x] => φ] = {
    byContradiction { existsNot: ∃[Any, [x] => ￢[φ]] =>
      theorem ∧ existsNot.value
    }
  }

  class PartiallyTyped[T <: D, D] {
    def instantiate[F[_ <: D]](forall: ∀[D, F]): F[T] = instUniv[D, F, T](forall)
    def generalize[F[_ <: D]](instance: F[T]): ∃[D, F] = genExist[D, F, T](instance)
  }

  def forType[T <: D, D] = new PartiallyTyped[T, D]

  class PartiallyTyped2[T1 <: D, T2 <: D, D] {
    def instantiate[F[_ <: D, _ <: D]](forall: ∀[D, [x <: D] => ∀[D, [y <: D] => F[x, y]]]): F[T1, T2] = {
      forType[T2, D].instantiate[[y <: D] => F[T1, y]](
        forType[T1, D].instantiate[[x <: D] => ∀[D, [y <: D] => F[x, y]]](forall)
      )
    }
    def generalize[F[_ <: D, _ <: D]](instance: F[T1, T2]): ∃[D, [x <: D] => ∃[D, [y <: D] => F[x, y]]] = {
      forType[T1, D].generalize[[x <: D] => ∃[D, [y <: D] => F[x, y]]](
        forType[T2, D].generalize[[y <: D] => F[T1, y]](instance)
      )
    }
  }

  def forType2[T1 <: D, T2 <: D, D] = new PartiallyTyped2[T1, T2, D]

  def notForall[D, φ[_ <: D]](notForall: ￢[∀[D, [x <: D] => φ[x]]]): ∃[D, [x <: D] => ￢[φ[x]]] = {
    eliminateDoubleNegation(notForall)
  }

  /**
    * ∃x.∃y.F(x, y) ⇔ ∃y.∃x.F(x, y)
    */
  def existsCommute[D, F[_ <: D, _ <: D]]: ∃[D, [x <: D] => ∃[D, [y <: D] => F[x, y]]] <=> ∃[D, [y <: D] => ∃[D, [x <: D] => F[x, y]]] = {
    def implies[G[_ <: D, _ <: D]]: ∃[D, [x <: D] => ∃[D, [y <: D] => G[x, y]]] => ∃[D, [w <: D] => ∃[D, [z <: D] => G[z, w]]] = { exists =>
      type X = exists.S
      val ev1: ∃[D, [y <: D] => G[X, y]] = exists.value

      type Y = ev1.S
      val ev2: G[X, Y] = ev1.value

      val ev3: ∃[D, [x <: D] => G[x, Y]] = forType[X, D].generalize[[x <: D] => G[x, Y]](ev2)
      forType[Y, D].generalize[[y <: D] => ∃[D, [x <: D] => G[x, y]]](ev3)
    }

    implies[F] ∧ implies[[X <: D, Y <: D] => F[Y, X]]
  }

  /**
    * ∀x.∀y.F(x, y) ⇔ ∀y.∀x.F(x, y)
    */
  def forallCommute[D,F[_ <: D, _ <: D]]: ∀[D, [x <: D] => ∀[D, [y <: D] => F[x, y]]] <=> ∀[D, [y <: D] => ∀[D, [x <: D] => F[x, y]]] = {
    def implies[G[_ <: D, _ <: D]] = eliminateDoubleNegation(
      byContradiction { negation: ￢[∀[D, [x <: D] => ∀[D, [y <: D] => G[x, y]]] => ∀[D, [y <: D] => ∀[D, [x <: D] => G[x, y]]]] =>
        val ev1 = nonImplication.implies(negation)
        val ev2: ∀[D, [x <: D] => ∀[D, [y <: D] => G[x, y]]] = ev1._1
        val ev3: ￢[∀[D, [y <: D] => ∀[D, [x <: D] => G[x, y]]]] = ev1._2
        val ev4: ∃[D, [y <: D] => ￢[∀[D, [x <: D] => G[x, y]]]] = notForall[D, [y <: D] => ∀[D, [x <: D] => G[x, y]]](ev3)
        type Y = ev4.S
        val ev5: ￢[∀[D, [x <: D] => G[x, Y]]] = ev4.value
        val ev6: ∃[D, [x <: D] => ￢[G[x, Y]]] = notForall[D, [x <: D] => G[x, Y]](ev5)
        type X = ev6.S
        val ev7: ￢[G[X, Y]] = ev6.value
        val ev8: G[X, Y] = forType[Y, D].instantiate[[y <: D] => G[X, y]](
          forType[X, D].instantiate[[x <: D] => ∀[D, [y <: D] => G[x, y]]](ev2)
        )
        ev8 ∧ ev7
      }
    )

    implies[F] ∧ implies[[X <: D, Y <: D] => F[Y, X]]
  }

}
