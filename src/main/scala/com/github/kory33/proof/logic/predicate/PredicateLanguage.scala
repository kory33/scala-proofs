package com.github.kory33.proof.logic.predicate

import com.github.kory33.proof.logic.propositional.LogicDefinitions._

/**
 * Language universe of a predicate logic system.
 */
trait PredicateLanguage {
  type Univ[_]

  trait ∃[F[_]] {
    val witness: Any
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
    def commute: B =::= A = sub[[a] => a =::= A](implicitly[A =::= A])
    def andThen[C](bEqC: B =::= C): A =::= C = bEqC.sub[[b] => A =::= b](this)
  }

  implicit def typeEq[A]: A =::= A = new =::=[A, A] {
    override def sub[F[_]] = identity
    override def commute = this
    override def andThen[C](aEqC: A =::= C) = aEqC
  }

  type ∃![F[_]] = ∃[F] ∧ ∀[[x] => ∀[[y] => (F[x] ∧ F[y]) => x =::= y]]

  /**
   * These two axioms are included to allow "definition" of new functional symbols.
   */
  def nameExistenceCond[P[_]](uniqueExistence: ∃![P]): P[{ type E = P }]
  def nameExistenceTerm[P[_]](uniqueExistence: ∃![P]): Univ[{ type E = P }]

  // Identity functional symbol
  type Id[z] = { type E[x] = z =::= x }
  object Id {
    val identity: ∀[[x] => x =::= Id[x]] = { x: Any => implicit xTerm: Univ[x.type] =>
      type F[y] = x.type =::= y
      val ev1: ∃[F] = genExist(x)
      val ev2: ∀[[y] => ∀[[z] => (F[y] ∧ F[z]) => y =::= z]] = {
        y: Any => implicit yTerm: Univ[y.type] => {
          z: Any => implicit zTerm: Univ[z.type] => {
            xEqyAndXEqZ: F[y.type] ∧ F[z.type] => {
              xEqyAndXEqZ._1.commute.andThen(xEqyAndXEqZ._2)
            }
          }
        }
      }
      val ev3: ∃![F] = ev1 ∧ ev2
      nameExistenceCond(ev3)
    }
  }
}
