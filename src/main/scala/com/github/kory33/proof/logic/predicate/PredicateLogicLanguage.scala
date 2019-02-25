package com.github.kory33.proof.logic.predicate

import scala.language.implicitConversions

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.ClassicalLogicSystem._

trait PredicateLogicLanguage {
  // typeclass of universe of language
  // We will sometimes say "object" to refer to a type within this particular universe
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

  trait ∀[P[_]] { def apply[X: Univ]: P[X] }

  implicit def negExistenceImpliesUniversality[P[_]](proof: ￢[∃[[x] => ￢[P[x]]]]): ∀[P] = new {
    def apply[X: Univ]: P[X] = { assumption: ￢[P[X]] => proof(assumption) }
  }

  // object type wrap
  type OWrap = { type T; val obj: Univ[T] }
  type WrappedProof[P[_]] = (OWrap => Any) { def apply(ow: OWrap): P[ow.T] }

  implicit def arbitraryTypeProofToUniversality[P[_]](proof: WrappedProof[P]): ∀[P] = new {
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

    def rightObject: Univ[B] = sub[Univ](leftObject)
  }

  implicit def identityEquality[A: Univ]: A =::= A = new {
    def sub[P[_]](proof: P[A]): P[A] = proof
    def commute: A =::= A = this
    def leftObject: Univ[A] = implicitly[Univ[A]]
  }

  type ∃![F[_]] = ∃[F] ∧ ∀[[x] => ∀[[y] => (F[x] ∧ F[y]) => x =::= y]]
}

