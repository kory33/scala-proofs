package com.github.kory33.proof.logic.predicate

import scala.language.implicitConversions
import scala.reflect.Selectable.reflectiveSelectable

import com.github.kory33.proof.logic.propositional.LogicDefinitions._

/**
 * Language universe of a predicate logic system.
 */
trait PredicateLanguage {
  type Univ[_]

  trait ∃[F[_]] {
    val witness: Any
    type W = witness.type
    val term: Univ[witness.type]
    val proof: F[witness.type]
  }

  def genExist[F[_]](x: Any)(implicit term: Univ[x.type], proof: F[x.type]): ∃[F] = {
    new ∃[F] {
      val witness: x.type = x
      val term: Univ[witness.type] = term
      val proof: F[witness.type] = proof
    }
  }

  type ∀[F[_]] = { def apply(x: Any): implicit Univ[x.type] => F[x.type] }
}

/**
 * Language universe of a predicate logic system with equality predicate.
 */
trait EqPredLanguage extends PredicateLanguage {
  trait =::=[A, B] {
    def sub[F[_]]: F[A] => F[B]
    def commute: B =::= A
    def andThen[C](bEqC: B =::= C): A =::= C = bEqC.sub[[b] => A =::= b](this)
    def cast(a: A): B = sub[[a] => a](a)
  }

  implicit def typeEq[A]: A =::= A = new =::=[A, A] {
    override def sub[F[_]] = identity
    override def commute = this
    override def andThen[C](aEqC: A =::= C) = aEqC
    override def cast(a: A): A = a
  }

  type ∃![F[_]] = ∃[F] ∧ ∀[[x] => ∀[[y] => (F[x] ∧ F[y]) => x =::= y]]

  def isomorphism[P[_]: ∃!](ex: ∃[P]): ex.witness.type =::= ∃[P]#W
  implicit def isomorphismTerm[P[_]](ex: ∃![P]): Univ[∃[P]#W]

  // Identity functional symbol
  type Id[z] = ∃[[x] => z =::= x]#W

  object Id {
    val uniqueness: ∀[[z] => ∃![[x] => z =::= x]] = {
      z: Any => implicit zTerm: Univ[z.type] =>
      type F[x] = z.type =::= x
      val existence: ∃[[x] => z.type =::= x] = genExist(z)
      val uniquenss: ∀[[x] => ∀[[y] => ((z.type =::= x) ∧ (z.type =::= y)) => x =::= y]] = {
        x: Any => implicit xTerm: Univ[x.type] => y: Any => implicit yTerm: Univ[y.type] => {
          xEqyAndXEqZ: F[x.type] ∧ F[y.type] => {
            xEqyAndXEqZ._1.commute.andThen(xEqyAndXEqZ._2)
          }
        }
      }
      existence ∧ uniquenss
    }
    val identity: ∀[[x] => x =::= Id[x]] = { z: Any => implicit zTerm: Univ[z.type] =>
      type F[x] = z.type =::= x
      implicit val ev1: ∃![[x] => z.type =::= x] = uniqueness(z)
      val ev2: z.type =::= ev1._1.witness.type = ev1._1.proof
      isomorphism(ev1._1).sub[[idx] => z.type =::= idx](ev2)
    }

    def id(x: Any)(implicit xu: Univ[x.type]): Id[x.type] = {
      implicit val ev1: ∃![[y] => x.type =::= y] = uniqueness(x)
      isomorphism(ev1._1).cast(ev1._1.witness)
    }
  }
}
