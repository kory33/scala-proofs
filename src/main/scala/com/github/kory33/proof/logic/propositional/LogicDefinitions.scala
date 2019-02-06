package com.github.kory33.proof.logic.propositional

object LogicDefinitions {

  type ￢[A] = A => Nothing
  type ∧[A, B] = (A, B)
  type ∨[A, B] = Either[A, B]
  type <=[A, B] = B => A
  type <=>[A, B] = (A => B) ∧ (B => A)

  implicit class Prop[A](instance: A) {
    def ∧[B](b: B): A ∧ B = (instance, b)
  }

  implicit class Equivalence[A, B](ev: A <=> B) {
    def implies: A => B = ev._1
    def impliedBy: B => A = ev._2
  }

}
