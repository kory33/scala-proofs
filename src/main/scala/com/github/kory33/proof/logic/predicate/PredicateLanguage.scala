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
  }

  type ∃![F[_]] = ∃[F] ∧ ∀[[x] => ∀[[y] => (F[x] ∧ F[y]) => x =::= y]]
}

trait EpsilonCalculus extends EqPredLanguage {
  type ε[P[_]]
  def epsilon[P[_]: ∃]: ε[P]
  def epsilonPred[P[_]](x: ε[P]): P[x.type]
  implicit def epsilonUniv[P[_]](implicit x: ε[P]): Univ[x.type]
  def epsilonUniqueness[P[_]: ∃!](x: ε[P]): x.type =::= ε[P]

  // Identity functional symbol
  type Id = [z] => ε[[x] => z =::= x]

  object Id {
    def existsId(x: Any)(implicit xu: Univ[x.type]): ∃[[y] => x.type =::= y] = genExist(x)

    val uniqueness: ∀[[z] => ∃![[x] => z =::= x]] = {
      z: Any => implicit zTerm: Univ[z.type] =>
      type F[x] = z.type =::= x
      val uniquenss: ∀[[x] => ∀[[y] => ((z.type =::= x) ∧ (z.type =::= y)) => x =::= y]] = {
        x: Any => implicit xTerm: Univ[x.type] => y: Any => implicit yTerm: Univ[y.type] => {
          xEqyAndXEqZ: F[x.type] ∧ F[y.type] => {
            xEqyAndXEqZ._1.commute.andThen(xEqyAndXEqZ._2)
          }
        }
      }
      existsId(z) ∧ uniquenss
    }

    val identity: ∀[[x] => x =::= Id[x]] = { implicit z: Any => implicit zTerm: Univ[z.type] =>
      type F[x] = z.type =::= x
      implicit val idz: ε[F] = epsilon[F](genExist(z))
      implicit val uniquenessEq: ∃![[x] => z.type =::= x] = uniqueness(z)
      epsilonUniqueness[F](idz).sub(epsilonPred(idz))
    }

    def id(x: Any)(implicit xUniv: Univ[x.type]): Id[x.type] = epsilon(existsId(x))

    def idid(x: Any)(implicit xUniv: Univ[x.type]): Id[Id[x.type]] = {
      implicit val idx: Id[x.type] = id(x)
      epsilonUniqueness(idx)(uniqueness(x)).sub(id(idx))
    }
  }
}
