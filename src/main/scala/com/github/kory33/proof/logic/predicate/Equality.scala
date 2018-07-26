package com.github.kory33.proof.logic.predicate

import scala.annotation.implicitNotFound

@implicitNotFound(msg = "Cannot prove that ${A} =::= ${B}.")
trait =::=[A, B] {
  def sub[F[_]]: F[A] => F[B]
}

object =::= {
  implicit def constructEquality[A]: A =::= A = new =::=[A, A] {
    def sub[F[_]]: F[A] => F[A] = identity
  }

  implicit class SubstitutablePredicate[F[_], A](fa: F[A]) {
    def sub[B](implicit ev: A =::= B): F[B] = ev.sub[F](fa)
  }
}
