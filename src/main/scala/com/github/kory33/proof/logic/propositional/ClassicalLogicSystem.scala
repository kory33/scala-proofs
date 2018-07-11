package com.github.kory33.proof.logic.propositional

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._

import scala.annotation.implicitNotFound

/**
  * Axiom system that can be inferred from intuitionistic logic and classical logic axiom
  */
object ClassicalLogicSystem {

  implicit def eliminateDoubleNegation[A](doubleNeg: ￢[￢[A]]): A = doubleNeg(a => return a)

  /**
    * law of exclusion of middle
    */
  def middleExclusion[A]: A ∨ ￢[A] = {
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

  def deMorgan3[A, B]: (￢[A] ∨ ￢[B]) ≣ ￢[A ∧ B] = {
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

  def implication[A, B]: (A => B) ≣ (￢[A] ∨ B) = {
    val implies = { ded: (A => B) => middleExclusion[A].commute.mapRight(ded) }
    val impliedBy: ￢[A] ∨ B => (A => B) = { 
      case Left(notA) => { a: A => explosion[B](a ∧ notA) }
      case Right(b) => alwaysImplied(b)
    }

    implies ∧ impliedBy
  }

  def nonImplication[A, B]: ￢[A => B] ≣ (A ∧ ￢[B]) = {
    val implies = { notDed: ￢[A => B] =>
      val ev1 = contraposition(implication[A, B].impliedBy)(notDed)
      deMorgan1.implies(ev1).mapLeft(eliminateDoubleNegation)
    }

    val impliedBy: (A ∧ ￢[B]) => ￢[A => B] = { case (a, notB) =>
      byContradiction { map: (A => B) =>
        map(a) ∧ notB
      }
    }

    implies ∧ impliedBy
  }

}
