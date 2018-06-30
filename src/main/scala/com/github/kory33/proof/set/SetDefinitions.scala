package com.github.kory33.proof.set

import com.github.kory33.proof.logic.propositional.LogicDefinitions._

object SetDefinitions {

  type Family

  type ∈[A, B]
  type ⊃[A, B]
  type ⊂[A, B] = B ⊃ A

  implicit class =#=[A, B](ev: (A ⊃ B) ∧ (A ⊂ B)) {
    def contains: A ⊃ B = ev._1

    def contained: A ⊂ B = ev._2
  }

  type =/=[A, B] = ￢[A =#= B]

}
