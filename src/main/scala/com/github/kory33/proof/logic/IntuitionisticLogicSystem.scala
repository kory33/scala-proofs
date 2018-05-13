package com.github.kory33.proof.logic

import com.github.kory33.proof.logic.LogicDefinitions._

/**
  * Axiom system that can be directly inferred from type system
  * i.e. basic theorems in intuitionistic logic
  */
class IntuitionisticLogicSystem {

  import IntuitionisticLogicSystem._

  final def identity[A]: A => A = { theorem: A => theorem }

  /**
    * Modus-Ponens
    */
  final def MP[A, B]: (A, A => B) => B = { (a, deduction) => deduction(a) }

  /**
    * Proof by contradiction
    */
  final def byContradiction[A]: (A => Nothing) => ￢[A] = identity

  /**
    * removal of disjunction
    */
  final def removeDisj[A, B, C](): (A ∨ B, A => C, B => C) => C = { (disj, deduc1, deduc2) =>
    disj match {
      case Left(a) => deduc1(a)
      case Right(b) => deduc2(b)
    }
  }

  final def explosion[A]: Nothing => A = _ => ???

  /**
    * law of noncontradiction
    */
  final def noncontradiction: ￢[Nothing] = identity

  /**
    * Modus tollens
    */
  final def MT[A, B]: (A => B) ∧ ￢[B] => ￢[A] = { case (ded, notB) =>
    val contradictory: A => Nothing = { a: A => (ded(a), notB) }
    byContradiction(contradictory)
  }

  final def contraposition[A, B]: (A => B) => (￢[B] => ￢[A]) = { ded => { notB => MT(ded ∧ notB) } }

  /**
    * Disjunctive syllogism / modus tollendo ponens
    */
  final def MTP[A, B]: ((A ∨ B) ∧ ￢[A]) => B = { case(disj, notA) =>
      disj match {
        case Left(a) => explosion(a ∧ notA)
        case Right(b) => b
      }
  }

  final def deMorgan1[A, B]: ￢[A ∨ B] ≣ (￢[A] ∧ ￢[B]) = {
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

  final def deMorgan2[A, B]: (￢[A] ∨ ￢[B]) => ￢[A ∧ B] = { disj =>
    val contradictory: A ∧ B => Nothing = { case(a, b) =>
      disj match {
        case Left(notA) => a ∧ notA
        case Right(notB) => b ∧ notB
      }
    }
    byContradiction(contradictory)
  }

  final def transitive[A, B, C]: ((A => B) ∧ (B => C)) => A => C = { case(f, g) => g compose f }

  final def distributive[A, B, C]: (A ∧ (B ∨ C)) ≣ ((A ∧ B) ∨ (A ∧ C)) = {
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

  /**
    * introduction of double negation
    */
  final def introduceDoubleNeg[A]: A => ￢[￢[A]] = { a: A =>
    val contradictory: ￢[A] => Nothing = { notA: ￢[A] => a ∧ notA }
    byContradiction(contradictory)
  }

}

object IntuitionisticLogicSystem {

  /**
    * Disjunctions
    */
  implicit def leftDisj[A, B](a: A): A ∨ B = Left(a)
  implicit def rightDisj[A, B](b: B): A ∨ B = Right(b)

  implicit def commuteDisj[A, B]: A ∨ B => B ∨ A = { conj => conj.swap }
  implicit def commuteConj[A, B]: A ∧ B => B ∧ A = { case (a, b) => (b, a) }

  implicit def contradiction[A]: A ∧ ￢[A] => Nothing = { case (a, notA) => notA(a) }

}