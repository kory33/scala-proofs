package com.github.kory33.proof.logic

import com.github.kory33.proof.logic.LogicDefinitions.{∧, _}
import com.github.kory33.proof.logic.LogicalImplications._

/**
  * Theorems that can be directly inferred from type system
  * i.e. basic theorems in intuitionistic logic
  */
object LogicTheorems {

  def identity[A]: A => A = { theorem: A => theorem }

  /**
    * Modus-Ponens
    */
  def MP[A, B]: (A, A => B) => B = { (a, deduction) => deduction(a) }

  /**
    * Proof by contradiction
    */
  def byContradiction[A]: (A => Nothing) => ￢[A] = identity

  /**
    * removal of disjunction
    */
  def removeDisj[A, B, C](): (A ∨ B, A => C, B => C) => C = { (disj, deduc1, deduc2) =>
    disj match {
      case Left(a) => deduc1(a)
      case Right(b) => deduc2(b)
    }
  }

  def explosion[A]: Nothing => A = _ => ???

  /**
    * law of noncontradiction
    */
  def noncontradiction: ￢[Nothing] = identity

  /**
    * Modus tollens
    */
  def MT[A, B]: (A => B) ∧ ￢[B] => ￢[A] = { case (ded, notB) =>
    val contradictory: A => Nothing = { a: A => (ded(a), notB) }
    byContradiction(contradictory)
  }

  def contraposition[A, B]: (A => B) => (￢[B] => ￢[A]) = { ded => { notB => MT(ded ∧ notB) } }

  /**
    * Disjunctive syllogism / modus tollendo ponens
    */
  def MTP[A, B]: ((A ∨ B) ∧ ￢[A]) => B = { case(disj, notA) =>
      disj match {
        case Left(a) => explosion(a ∧ notA)
        case Right(b) => b
      }
  }

  def deMorgan1[A, B]: ￢[A ∨ B] ≣ (￢[A] ∧ ￢[B]) = {
    val implies: ￢[A ∨ B] => (￢[A] ∧ ￢[B]) = { contradictory: (A ∨ B => Nothing) =>
      val notA = { a: A => contradictory(a) }
      val notB = { b: B => contradictory(b) }
      notA ∧ notB
    }
    val impliedBy: ￢[A ∨ B] <= (￢[A] ∧ ￢[B]) = { case(notA, notB) =>
        val contradictory: A ∨ B => Nothing = {
          case Left(a) => a ∧ notA
          case Right(b) => b ∧ notB
        }
        byContradiction(contradictory)
    }

    implies ∧ impliedBy
  }

  def deMorgan2[A, B]: (￢[A] ∨ ￢[B]) => ￢[A ∧ B] = { disj =>
    val contradictory: A ∧ B => Nothing = { case(a, b) =>
      disj match {
        case Left(notA) => a ∧ notA
        case Right(notB) => b ∧ notB
      }
    }
    byContradiction(contradictory)
  }

  def transitive[A, B, C]: ((A => B) ∧ (B => C)) => A => C = { case(f, g) => g compose f }

  def distributive[A, B, C]: (A ∧ (B ∨ C)) ≣ ((A ∧ B) ∨ (A ∧ C)) = {
    val implies: (A ∧ (B ∨ C)) => ((A ∧ B) ∨ (A ∧ C)) = { case(a, bOrC) =>
      bOrC match {
        case Left(b) => a ∧ b
        case Right(c) => a ∧ c
      }
    }
    val impliedBy: (A ∧ (B ∨ C)) <= ((A ∧ B) ∨ (A ∧ C)) = {
      case Left((a, b)) => a ∧ b
      case Right((a, c)) => a ∧ c
    }

    implies ∧ impliedBy
  }

}
