package com.github.kory33.experimental.proof.logic.predicate

import scala.annotation.implicitNotFound
import com.github.kory33.proof.set.Σ

object Equality {
  /**
   * Typeclass for equality predicate
   */
  @implicitNotFound(msg = "Cannot prove that ${A} =::= ${B}.")
  trait =::=[A, B] {
    def sub[F[_]]: F[A] => F[B]
    def commute: =::=[B, A] = this.sub[[b] => =::=[b, A]](implicitly[=::=[A, A]])
    def andThen[C](next: =::=[B, C]): =::=[A, C] = next.sub[[c] => =::=[A, c]](this)
  }

  object =::= {
    implicit def constructEquality[A]: =::=[A, A] = new =::=[A, A] {
      def sub[F[_]]: F[A] => F[A] = identity
    }
  }

}
