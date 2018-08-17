package com.github.kory33.proof.logic.propositional

import scala.language.implicitConversions

import com.github.kory33.proof.logic.propositional.LogicDefinitions._

/**
  * Axiom system that can be directly inferred from type system
  * i.e. basic theorems in intuitionistic logic
  */
object IntuitionisticLogicSystem {

  final def identity[A]: A => A = { theorem: A => theorem }

  /**
    * Modus-Ponens
    */
  final def MP[A, B]: A => (A => B) => B = { a => deduction => deduction(a) }

  implicit def contradiction[A](contr: A ∧ ￢[A]): Nothing = contr match { case (a, notA) => notA(a) }

  /**
    * Proof by contradiction
    */
  final def byContradiction[A]: (A => Nothing) => ￢[A] = identity

  /**
    * Disjunctions
    */
  implicit def leftDisj[A, B](a: A): A ∨ B = Left(a)
  implicit def rightDisj[A, B](b: B): A ∨ B = Right(b)
  implicit class RichDisjunction[A, B](disj: A ∨ B) {
    def commute: B ∨ A = disj.swap
    def mapRight[C]: (B => C) => A ∨ C = { ded => disj.map(ded) }
    def mapLeft[C] : (A => C) => C ∨ B = { ded => disj.commute.mapRight(ded).commute }
  }

  implicit class RichConjunction[A, B](conj: A ∧ B) {
    def commute: B ∧ A = conj match { case (a, b) => (b, a) }
    def mapRight[C]: (B => C) => A ∧ C = { ded => conj match { case (a, b) => (a, ded(b)) } }
    def mapLeft[C] : (A => C) => C ∧ B = { ded => conj.commute.mapRight(ded).commute }
  }

  implicit class RichEquivalence[A, B](eq: A <=> B) {
    def andThen[C]: (B <=> C) => (A <=> C) = { bEqC => eq.implies.andThen(bEqC.implies) ∧ bEqC.impliedBy.andThen(eq.impliedBy) }
    def commute: B <=> A = eq.impliedBy ∧ eq.implies
  }

  /**
    * removal of disjunction
    */
  final def removeDisj[A, B, C]: A ∨ B => (A => C) => (B => C) => C = { disj => deduc1 => deduc2 =>
    disj match {
      case Left(a) => deduc1(a)
      case Right(b) => deduc2(b)
    }
  }

  final def explosion[A]: Nothing => A = identity

  /**
    * law of noncontradiction
    */
  final def noncontradiction: ￢[Nothing] = identity

  /**
    * Modus tollens
    */
  final def MT[A, B]: (A => B) => ￢[B] => ￢[A] = { ded => notB =>
    byContradiction { a: A => (ded(a), notB) }
  }

  final def contraposition[A, B]: (A => B) => (￢[B] => ￢[A]) = { ded => { notB => MT(ded)(notB) } }

  /**
    * Disjunctive syllogism / modus tollendo ponens
    */
  final def MTP[A, B]: (A ∨ B) => ￢[A] => B = { disj => notA =>
      disj match {
        case Left(a) => explosion(a ∧ notA)
        case Right(b) => b
      }
  }

  final def deMorgan1[A, B]: ￢[A ∨ B] <=> (￢[A] ∧ ￢[B]) = {
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

  final def transitive[A, B, C]: (A => B) => (B => C) => A => C = { f => g => g compose f }

  final def distributive[A, B, C]: (A ∧ (B ∨ C)) <=> ((A ∧ B) ∨ (A ∧ C)) = {
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

  final def alwaysImplied[A, B]: B => (A => B) = { b: B => _ => b }

}
