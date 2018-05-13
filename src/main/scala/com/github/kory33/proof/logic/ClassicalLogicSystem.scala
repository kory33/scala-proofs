package com.github.kory33.proof.logic

import com.github.kory33.proof.logic.LogicDefinitions._
import com.github.kory33.proof.logic.IntuitionisticLogicSystem._

import scala.annotation.implicitNotFound

/**
  * Axiom system that can be inferred from intuitionistic logic and classical logic axiom
  */
class ClassicalLogicSystem(implicit val axiom: ClassicalLogicAxiom) extends IntuitionisticLogicSystem {

  import ClassicalLogicSystem._

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

object ClassicalLogicSystem {

  @implicitNotFound(msg = "Classical logic axiom missing")
  implicit def eliminateDoubleNegation[A](doubleNeg: ￢[￢[A]])(implicit axiom: ClassicalLogicAxiom): A = {
    axiom.eliminateDoubleNegation(doubleNeg)
  }

}
