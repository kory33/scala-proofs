package com.github.kory33.proof.logic

import com.github.kory33.proof.logic.LogicDefinitions.{∧, ∨, ￢}

/**
  * implications that can be inferred directly from type system
  */
object LogicalImplications {

  /**
    * Disjunctions
    */
  implicit def leftDisj[A, B](a: A): A ∨ B = Left(a)
  implicit def rightDisj[A, B](b: B): A ∨ B = Right(b)

  implicit def commuteDisj[A, B]: A ∨ B => B ∨ A = { conj => conj.swap }
  implicit def commuteConj[A, B]: A ∧ B => B ∧ A = { case (a, b) => (b, a) }

  implicit def contradiction[A]: A ∧ ￢[A] => Nothing = { case (a, notA) => notA(a) }

}
