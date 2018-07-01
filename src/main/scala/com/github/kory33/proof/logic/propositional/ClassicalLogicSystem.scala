package com.github.kory33.proof.logic.propositional

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._

import scala.annotation.implicitNotFound

/**
  * Axiom system that can be inferred from intuitionistic logic and classical logic axiom
  */
object ClassicalLogicSystem {

  implicit def eliminateDoubleNegation[A](doubleNeg: ￢[￢[A]])(implicit axiom: ClassicalLogicAxiom): A = {
    axiom.eliminateDoubleNegation(doubleNeg)
  }

  /**
    * law of exclusion of middle
    */
  def middleExclusion[A](implicit axiom: ClassicalLogicAxiom): A ∨ ￢[A] = {
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

  def deMorgan3[A, B](implicit axiom: ClassicalLogicAxiom): (￢[A] ∨ ￢[B]) ≣ ￢[A ∧ B] = {
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

  def implication[A, B](implicit axiom: ClassicalLogicAxiom): (A => B) ≣ (￢[A] ∨ B) = {
    val implies = { ded: (A => B) => middleExclusion[A].commuteDisj.mapRight(ded) }
    val impliedBy: ￢[A] ∨ B => (A => B) = { 
      case notA: ￢[A] => { a: A => explosion[B](a ∧ notA) }
      case b: B => alwaysImplied(b)
    }

    implies ∧ impliedBy
  }

}
