package com.github.kory33.proof.set

import com.github.kory33.proof.logic.predicate.PredicateLogicDefinitions.{∃, _}
import com.github.kory33.proof.logic.predicate.PredicateLogicSystem._
import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set.ZFAxiom._

object ZFSystem {
  /**
    * There exists an empty set.
    */
  def existsEmpty(implicit axiom: ZFAxiom): ∃[isEmpty] = {
    val separated = separation[[_, _] => Nothing]
    val set = existence

    type Set = set.S

    val emptyExistence: ∃[[y] => ∀[[u] => (u ∈ y) ≣ ((u ∈ Set) ∧ Nothing)]] =
      forType[Nothing].instantiate[[p] => ∃[[y] => ∀[[u] => (u ∈ y) ≣ ((u ∈ Set) ∧ Nothing)]]](
        forType[Set].instantiate[[x] => ∀[[p] => ∃[[y] => ∀[[u] => (u ∈ y) ≣ ((u ∈ x) ∧ Nothing)]]]](separated)
      )

    type EmptySet = emptyExistence.S
    val ev1: ∀[[u] => (u ∈ EmptySet) ≣ ((u ∈ Set) ∧ Nothing)] = emptyExistence.value
    val ev2: ∀[[u] => (u ∈ EmptySet) => Nothing] = byContradiction { assumption: ∃[[u] => ￢[u ∈ EmptySet] => Nothing] =>
      type U = assumption.S
      val ev21 = assumption.value
      val ev22 = forType[U].instantiate[[u] => (u ∈ EmptySet) ≣ ((u ∈ Set) ∧ Nothing)](ev1)
      val ev23 = ev22.implies.andThen { conclusion: (U ∈ Set) ∧ Nothing => conclusion._2 }
      ev21(ev23)
    }
    val ev3: ∀[[u] => u ∉ EmptySet] = ev2
  
    forType[EmptySet].generalize[[x] => ∀[[y] => y ∉ x]](ev3)
  }

  /**
   * There is no set of all sets.
   */
  def noSetOfAllSets(implicit axiom: ZFAxiom): ￢[∃[[x] => ∀[[y] => y ∈ x]]] = {
    def lemma1[A, B]: ￢[(A ≣ (B ∧ ￢[A])) ∧ B] = byContradiction { assumption: (A ≣ (B ∧ ￢[A])) ∧ B =>
      val (aEqBAndNotA, b) = assumption
      def ev1: ￢[A] => A = { notA: ￢[A] => aEqBAndNotA.impliedBy(b ∧ notA) }
      def ev2: A => ￢[A] = { a: A => aEqBAndNotA.implies(a)._2 }
      val notAEqNotA = byContradiction { aEqNotA: A ≣ ￢[A] =>
        val notA = byContradiction { a: A => a ∧ aEqNotA.implies(a) }
        val a: A = aEqNotA.impliedBy(notA)
        a ∧ notA
      }
      notAEqNotA(ev2 ∧ ev1)
    }

    byContradiction { assumption: ∃[[x] => ∀[[y] => y ∈ x]] =>
      type S = assumption.S
      val setOfAllSets = assumption.value

      val paradoxicalExistence: ∃[[z] => ∀[[u] => (u ∈ z) ≣ ((u ∈ S) ∧ (u ∉ u))]] = 
        forType[Nothing].instantiate[[p] => ∃[[y] => ∀[[u] => (u ∈ y) ≣ ((u ∈ S) ∧ (u ∉ u))]]](
          forType[S].instantiate[[x] => ∀[[p] => ∃[[y] => ∀[[u] => (u ∈ y) ≣ ((u ∈ x) ∧ (u ∉ u))]]]](
            separation[[X, _] => X ∉ X]
          )
        )
      type Z = paradoxicalExistence.S
      val paradoxicalSet: ∀[[u] => (u ∈ Z) ≣ ((u ∈ S) ∧ (u ∉ u))] = paradoxicalExistence.value
      val ev1: (Z ∈ Z) ≣ ((Z ∈ S) ∧ (Z ∉ Z)) = forType[Z].instantiate[[u] => (u ∈ Z) ≣ ((u ∈ S) ∧ (u ∉ u))](paradoxicalSet)
      val ev2: Z ∈ S = forType[Z].instantiate[[y] => y ∈ S](setOfAllSets)
      lemma1(ev1 ∧ ev2)
    }
  }
}