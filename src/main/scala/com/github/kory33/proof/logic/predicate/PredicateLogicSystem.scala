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
  implicit def genExist[D[_], F[_], A : D](instance: F[A]): ∃[D, F] = new ∃ { type S = A; val instance = instance; val typeclass = implicitly }

  def instUniv[D[_], φ[_], X : D](forall: ∀[D, φ]): φ[X] = {
    byContradiction { notPX: ￢[φ[X]] =>
      val ev11: ∃[D, [x] => ￢[φ[x]]] = notPX
      val ev12: ￢[∃[D, [x] => ￢[φ[x]]]] = forall
      ev11 ∧ ev12
    }
  }

  implicit def existentialDomain[D[_], F[_]](implicit existence: ∃[D, F]): D[existence.S] = existence.typeclass

  /**
    * Existential instantiation(elimination)
    */
  def instExist[D[_], F[_], φ](implicit exists: ∃[D, F], forall: ∀[D, [X] => F[X] => φ]): φ = {
    val ev1: F[exists.S] => φ = instUniv[D, [x] => F[x] => φ, exists.S](forall)
    ev1(exists.instance)
  }

  class PartiallyTyped[D[_], T : D] {
    def instantiate[F[_]](forall: ∀[D, F]): F[T] = instUniv[D, F, T](forall)
    def generalize[F[_]](instance: F[T]): ∃[D, F] = genExist[D, F, T](instance)
  }

  def forType[D[_], T : D] = new PartiallyTyped[D, T]

  class PartiallyTyped2[D[_], T1 : D, T2 : D] {
    def instantiate[F[_, _]](forall: ∀[D, [x] => ∀[D, [y] => F[x, y]]]): F[T1, T2] = {
      forType[D, T2].instantiate[[y] => F[T1, y]](
        forType[D, T1].instantiate[[x] => ∀[D, [y] => F[x, y]]](forall)
      )
    }
    def generalize[F[_, _]](instance: F[T1, T2]): ∃[D, [x] => ∃[D, [y] => F[x, y]]] = {
      forType[D, T1].generalize[[x] => ∃[D, [y] => F[x, y]]](
        forType[D, T2].generalize[[y] => F[T1, y]](instance)
      )
    }
  }

  def forType2[D[_], T1 : D, T2 : D] = new PartiallyTyped2[D, T1, T2]

  def notForall[D[_], φ[_]](notForall: ￢[∀[D, [x] => φ[x]]]): ∃[D, [x] => ￢[φ[x]]] = {
    eliminateDoubleNegation(notForall)
  }

  def notForall2[D[_], φ[_, _]](notForall: ￢[∀[D, [x] => ∀[D, [y] => φ[x, y]]]]): ∃[D, [x] => ∃[D, [y] => ￢[φ[x, y]]]] = {
    implicit val ev1: ∃[D, [x] => ￢[∀[D, [y] => φ[x, y]]]] = notForall
    type X = ev1.S
    val ev2: ∃[D, [y] => ￢[φ[X, y]]] = ev1.instance
    forType[D, X].generalize[[x] => ∃[D, [y] => ￢[φ[x, y]]]](ev2)
  }

  def notForall3[D[_], φ[_, _, _]](notForall: ￢[∀[D, [x] => ∀[D, [y] => ∀[D, [z] => φ[x, y, z]]]]])
    : ∃[D, [x] => ∃[D, [y] => ∃[D, [z] => ￢[φ[x, y, z]]]]] = {
    implicit val ev1: ∃[D, [x] => ￢[∀[D, [y] => ∀[D, [z] => φ[x, y, z]]]]] = notForall
    type X = ev1.S
    val ev2: ￢[∀[D, [y] => ∀[D, [z] => φ[X, y, z]]]] = ev1.instance
    val ev3: ∃[D, [y] => ∃[D, [z] => ￢[φ[X, y, z]]]] = notForall2[D, [y, z] => φ[X, y, z]](ev2)
    forType[D, X].generalize[[x] => ∃[D, [y] => ∃[D, [z] => ￢[φ[x, y, z]]]]](ev3)
  }

  def notForall4[D[_], φ[_, _, _, _]](notForall: ￢[∀[D, [x] => ∀[D, [y] => ∀[D, [z] => ∀[D, [w] => φ[x, y, z, w]]]]]])
    : ∃[D, [x] => ∃[D, [y] => ∃[D, [z] => ∃[D, [w] => ￢[φ[x, y, z, w]]]]]] = {
    implicit val ev1: ∃[D, [x] => ￢[∀[D, [y] => ∀[D, [z] => ∀[D, [w] => φ[x, y, z, w]]]]]] = notForall
    type X = ev1.S
    val ev2: ￢[∀[D, [y] => ∀[D, [z] => ∀[D, [w] => φ[X, y, z, w]]]]] = ev1.instance
    val ev3: ∃[D, [y] => ∃[D, [z] => ∃[D, [w] => ￢[φ[X, y, z, w]]]]] = notForall3[D, [y, z, w] => φ[X, y, z, w]](ev2)
    forType[D, X].generalize[[x] => ∃[D, [y] => ∃[D, [z] => ∃[D, [w] => ￢[φ[x, y, z, w]]]]]](ev3)
  }

  /**
    * ∃x.∃y.F(x, y) ⇔ ∃y.∃x.F(x, y)
    */
  def existsCommute[D[_], F[_, _]]: ∃[D, [x] => ∃[D, [y] => F[x, y]]] <=> ∃[D, [y] => ∃[D, [x] => F[x, y]]] = {
    def implies[G[_, _]]: ∃[D, [x] => ∃[D, [y] => G[x, y]]] => ∃[D, [w] => ∃[D, [z] => G[z, w]]] = { implicit exists =>
      type X = exists.S
      implicit val ev1: ∃[D, [y] => G[X, y]] = exists.instance

      type Y = ev1.S
      val ev2: G[X, Y] = ev1.instance

      val ev3: ∃[D, [x] => G[x, Y]] = forType[D, X].generalize[[x] => G[x, Y]](ev2)
      forType[D, Y].generalize[[y] => ∃[D, [x] => G[x, y]]](ev3)
    }

    implies[F] ∧ implies[[X, Y] => F[Y, X]]
  }

  /**
    * ∀x.∀y.F(x, y) ⇔ ∀y.∀x.F(x, y)
    */
  def forallCommute[D[_], F[_, _]]: ∀[D, [x] => ∀[D, [y] => F[x, y]]] <=> ∀[D, [y] => ∀[D, [x] => F[x, y]]] = {
    def implies[G[_, _]] = eliminateDoubleNegation(
      byContradiction { negation: ￢[∀[D, [x] => ∀[D, [y] => G[x, y]]] => ∀[D, [y] => ∀[D, [x] => G[x, y]]]] =>
        val ev1 = nonImplication.implies(negation)
        val ev2: ∀[D, [x] => ∀[D, [y] => G[x, y]]] = ev1._1
        val ev3: ￢[∀[D, [y] => ∀[D, [x] => G[x, y]]]] = ev1._2
        implicit val ev4: ∃[D, [y] => ￢[∀[D, [x] => G[x, y]]]] = notForall[D, [y] => ∀[D, [x] => G[x, y]]](ev3)
        type Y = ev4.S
        val ev5: ￢[∀[D, [x] => G[x, Y]]] = ev4.instance
        implicit val ev6: ∃[D, [x] => ￢[G[x, Y]]] = notForall[D, [x] => G[x, Y]](ev5)
        type X = ev6.S
        val ev7: ￢[G[X, Y]] = ev6.instance
        val ev8: G[X, Y] = forType[D, Y].instantiate[[y] => G[X, y]](
          forType[D, X].instantiate[[x] => ∀[D, [y] => G[x, y]]](ev2)
        )
        ev8 ∧ ev7
      }
    )

    implies[F] ∧ implies[[X, Y] => F[Y, X]]
  }

}
