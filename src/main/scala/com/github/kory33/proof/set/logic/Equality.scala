package com.github.kory33.proof.set.logic

import scala.annotation.implicitNotFound
import com.github.kory33.proof.set.Σ

@implicitNotFound(msg = "Cannot prove that ${A} =::= ${B}.")
trait =::=[A <: Σ, B <: Σ] {
  def sub[F[_ <: Σ]]: F[A] => F[B]
  def commute: B =::= A
}

object =::= {
  implicit def constructEquality[A <: Σ]: =::=[A, A] = new =::=[A, A] {
    def sub[F[_ <: Σ]]: F[A] => F[A] = identity
    def commute: A =::= A = this
  }
}
