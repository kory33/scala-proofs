package com.github.kory33.proof.logic.predicate

import scala.annotation.implicitNotFound
import com.github.kory33.proof.set.Σ

object Equality {
  /**
  * Typeclass of bounded isomorphism
  */
  @implicitNotFound(msg = "Cannot prove that ${A} =::= ${B}.")
  trait =::=[D, A <: D, B <: D] {
    def lift[F[_ <: D] <: D]: =::=[D, F[A], F[B]]
    def sub[F[_ <: D]]: F[A] => F[B]
    def commute: =::=[D, B, A]
  }

  object =::= {
    implicit def constructEquality[D, A <: D]: =::=[D, A, A] = new =::=[D, A, A] {
      def lift[F[_ <: D] <: D]: =::=[D, F[A], F[A]] = constructEquality[D, F[A]]
      def sub[F[_ <: D]]: F[A] => F[A] = identity
      def commute: =::=[D, A, A] = this
    }
  }

  /**
   * unbounded isomorphism
   */
  type =~=[A, B] = =::=[Any, A, B]

}
