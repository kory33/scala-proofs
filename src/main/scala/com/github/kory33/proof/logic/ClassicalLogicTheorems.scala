package com.github.kory33.proof.logic

import com.github.kory33.proof.logic.LogicDefinitions._
import com.github.kory33.proof.logic.LogicalImplications._
import com.github.kory33.proof.logic.ClassicalLogicImplications._

class ClassicalLogicTheorems(implicit val axiom: ClassicalLogicAxiom) extends LogicTheorems {

  /**
    * law of exclusion of middle
    */
  final def middleExclusion[A]: A ∨ ￢[A] = {
    val contradictory1: ￢[A ∨ ￢[A]] => Nothing = { negProp =>
      val contradictory2: ￢[A] => Nothing = { notA =>
        val prop: A ∨ ￢[A] = notA
        prop ∧ negProp
      }
      val a: A = byContradiction(contradictory2)
      val prop: A ∨ ￢[A] = a
      prop ∧ negProp
    }
    byContradiction(contradictory1)
  }

  final def deMorgan3[A, B]: (￢[A] ∨ ￢[B]) ≣ ￢[A ∧ B] = {
    val implies = deMorgan2[A, B]
    val impliedBy: (￢[A] ∨ ￢[B]) <= ￢[A ∧ B] = { notConj =>
      val contradictory: ￢[￢[A] ∨ ￢[B]] => Nothing = { prop =>
        val doubleNotConj = deMorgan1[￢[A], ￢[B]].implies(prop)
        val a: A = doubleNotConj._1
        val b: B = doubleNotConj._2
        (a ∧ b) ∧ notConj
      }
      byContradiction(contradictory)
    }

    implies ∧ impliedBy
  }

}
