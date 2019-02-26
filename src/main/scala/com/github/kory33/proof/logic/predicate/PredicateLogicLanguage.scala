package com.github.kory33.proof.logic.predicate

import scala.language.implicitConversions
import scala.reflect.Selectable.reflectiveSelectable

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.ClassicalLogicSystem._

trait PredicateLogicLanguage {
  // typeclass of universe of language
  // We will sometimes say "object" to refer to a type within this particular universe.
  type Univ[_]

  trait ∃[P[_]] {
    type W

    // proof that W satisfies P
    val proof: P[W]

    // W is an object in the language
    val obj: Univ[W]
  }

  implicit def genExist[P[_], X: Univ](proofX: P[X]): ∃[P] = new {
    type W = X
    val proof = proofX
    val obj: Univ[X] = implicitly
  }

  trait ∀[P[_]] { def apply[X](implicit ev: Univ[X]): P[X] }

  implicit def noCounterexample[P[_]](proof: ￢[∃[[x] => ￢[P[x]]]]): ∀[P] = new {
    def apply[X: Univ]: P[X] = { assumption: ￢[P[X]] => proof(assumption) }
  }

  // object type wrap
  type OWrap = { type T; val obj: Univ[T] }
  type WrappedProof[P[_]] = (OWrap => Any) { def apply(ow: OWrap): P[ow.T] }

  implicit def genUniv[P[_]](proof: WrappedProof[P]): ∀[P] = new {
    def apply[X: Univ]: P[X] = {
      val ow: OWrap { type T = X } = new { type T = X; val obj: Univ[T] = implicitly }
      proof(ow)
    }
  }
}

trait EqualityPredicateLanguage extends PredicateLogicLanguage {
  trait =::=[A, B] {
    def sub[P[_]](proof: P[A]): P[B]
    def commute: B =::= A
    def leftObject: Univ[A]

    def andThen[C](bEqC: B =::= C): A =::= C = bEqC.sub(this)
    def rightObject: Univ[B] = sub[Univ](leftObject)
  }

  implicit def identityEquality[A: Univ]: A =::= A = new {
    def sub[P[_]](proof: P[A]): P[A] = proof
    def commute: A =::= A = this
    def leftObject: Univ[A] = implicitly[Univ[A]]
  }

  type ∃![F[_]] = ∃[F] ∧ ∀[[x] => ∀[[y] => (F[x] ∧ F[y]) => x =::= y]]
}

/**
 * Language system which utilises type projection in a way somewhat similar to epsilon operator.
 * The difference here is that projection may only be an object when the existence is known to be unique(no "choosing" is done except on a singleton).
 *
 * This language imposes another constraint on type equality, which is named as projectionEquality
 */
trait ProjectiveCalculusLanguage extends EqualityPredicateLanguage {
  type Proj[P[_]] = ∃[P]#W

  // axiom of projection equality
  def projectionEquality[P[_]: ∃!, W: Univ](proof: P[W]): W =::= Proj[P]

  def projectionSubstitution[P[_]: ∃!]: P[Proj[P]] = {
    val existence: ∃[P] = implicitly[∃![P]]._1
    type W = existence.W
    implicit val objW: Univ[W] = existence.obj
    val ev1: P[W] = existence.proof
    projectionEquality(ev1).sub(ev1)
  }

  implicit def projectionObject[P[_]: ∃!]: Univ[Proj[P]] = {
    val existence: ∃[P] = implicitly[∃![P]]._1
    type W = existence.W
    implicit val objW: Univ[W] = existence.obj
    projectionEquality(existence.proof).sub(existence.obj)
  }

  /**
   * a minimal example of the axiom in use.
   *
   * Id here is not an ordinary type constructor [x] => x;
   * instead, it "projects" all types that are (propositionally) equal to the argument type.
   */
  type Id = [x] => Proj[[y] => x =::= y]
  object Id {
    val uniqueExistence: ∀[[x] => ∃![[y] => x =::= y]] = genUniv { x: OWrap => type X = x.T
      implicit val objX: Univ[X] = x.obj
      val ev1: ∃[[y] => X =::= y] = genExist(implicitly[X =::= X])
      val ev2: ∀[[z] => ∀[[w] => ((X =::= z) ∧ (X =::= w)) => z =::= w]] = {
        genUniv { z: OWrap => genUniv { w: OWrap => { case (xEqZ, xEqW) => xEqZ.commute.andThen(xEqW) } } }
      }
      ev1 ∧ ev2
    }

    val identity: ∀[[x] => x =::= Id[x]] = genUniv { x: OWrap => projectionSubstitution(uniqueExistence[x.T](x.obj)) }
    implicit def identityObj[X: Univ]: Univ[Id[X]] = projectionObject(uniqueExistence[X])
  }
}
