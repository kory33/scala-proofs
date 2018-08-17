package com.github.kory33.proof.logic.predicate

import scala.annotation.implicitNotFound
import com.github.kory33.proof.set.Σ

object Equality {
  /**
  * Typeclass of bounded isomorphism
  */
  @implicitNotFound(msg = "Cannot prove that ${A} =::= ${B}.")
  trait =::=[D, A <: D, B <: D] {
    def sub[F[_ <: D]]: F[A] => F[B]
    def commute: =::=[D, B, A] = this.sub[[b <: D] => =::=[D, b, A]](implicitly[=::=[D, A, A]])
  }

  object =::= {
    implicit def constructEquality[D, A <: D]: =::=[D, A, A] = new =::=[D, A, A] {
      def sub[F[_ <: D]]: F[A] => F[A] = identity
    }
  }

  /**
   * unbounded isomorphism
   */
  type =~=[A, B] = =::=[Any, A, B]

}
