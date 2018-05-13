package com.github.kory33.proof.logic

object LogicDefinitions {

  type ￢[A] = A => Nothing
  type ∧[A, B] = (A, B)
  type ∨[A, B] = Either[A, B]
  type <=[A, B] = B => A

  implicit class Theorem[A](instance: A) {
    def ∧[B](b: B): A ∧ B = (instance, b)
  }

  implicit class ≣[A, B](ev: (A => B) ∧ (B => A)) {
    def implies: A => B = ev._1
    def impliedBy: B => A = ev._2
  }

}
