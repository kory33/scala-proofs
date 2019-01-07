package com.github.kory33.proof.logic.predicate

import com.github.kory33.proof.logic.propositional.LogicDefinitions._

/**
 * Language universe of a predicate logic system.
 */
trait PredicateLanguage {
    type Obj <: AnyRef

    trait Term[x <: AnyRef]
    implicit def objIsTerm(implicit x: Obj): Term[x.type]

    trait ∃[F[_]] {
        val witness: AnyRef
        val term: Term[witness.type]
        val proof: F[witness.type]
    }

    type ∀[F[_]] = { def apply(x: AnyRef)(implicit t: Term[x.type]): F[x.type] }
}

/**
 * Language universe of a predicate logic system with equality predicate.
 */
trait EqPredLanguage extends PredicateLanguage {
    trait =::=[A, B] {
        def sub[F[_]]: F[A] => F[B]
        def commute: B =::= A = sub[λ[a => a =::= A]](implicitly[A =::= A])
        def andThen[C](bEqC: B =::= C): A =::= C = bEqC.sub[λ[b => A =::= b]](this)
    }
    implicit def typeEq[A]: A =::= A = new =::=[A, A] {
        override def sub[F[_]] = identity
        override def commute = this
        override def andThen[C](aEqC: A =::= C) = aEqC
    }
}
