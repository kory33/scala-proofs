package com.github.kory33.proof.set

import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateSystem._
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

    val emptyExistence: ∃[[y <: Σ] => ∀[[u <: Σ] => (u ∈ y) <=> ((u ∈ Set) ∧ Nothing)]] =
      forType[Set].instantiate[[p <: Σ] => ∃[[y <: Σ] => ∀[[u <: Σ] => (u ∈ y) <=> ((u ∈ Set) ∧ Nothing)]]](
        forType[Set].instantiate[[x <: Σ] => ∀[[p <: Σ] => ∃[[y <: Σ] => ∀[[u <: Σ] => (u ∈ y) <=> ((u ∈ x) ∧ Nothing)]]]](separated)
      )

    type EmptySet = emptyExistence.S
    val ev1: ∀[[u <: Σ] => (u ∈ EmptySet) <=> ((u ∈ Set) ∧ Nothing)] = emptyExistence.value
    val ev2: ∀[[u <: Σ] => (u ∈ EmptySet) => Nothing] = byContradiction { assumption: ∃[[u <: Σ] => ￢[u ∈ EmptySet] => Nothing] =>
      type U = assumption.S
      val ev21 = assumption.value
      val ev22 = forType[U].instantiate[[u <: Σ] => (u ∈ EmptySet) <=> ((u ∈ Set) ∧ Nothing)](ev1)
      val ev23 = ev22.implies.andThen { conclusion: (U ∈ Set) ∧ Nothing => conclusion._2 }
      ev21(ev23)
    }
    val ev3: ∀[[u <: Σ] => u ∉ EmptySet] = ev2
  
    forType[EmptySet].generalize[[x <: Σ] => ∀[[y <: Σ] => y ∉ x]](ev3)
  }

  /**
   * There is no set of all sets.
   */
  def noSetOfAllSets(implicit axiom: ZFAxiom): ￢[∃[[x <: Σ] => ∀[[y <: Σ] => y ∈ x]]] = {
    def lemma1[A, B]: ￢[(A <=> (B ∧ ￢[A])) ∧ B] = byContradiction { assumption: (A <=> (B ∧ ￢[A])) ∧ B =>
      val (aEqBAndNotA, b) = assumption
      def ev1: ￢[A] => A = { notA: ￢[A] => aEqBAndNotA.impliedBy(b ∧ notA) }
      def ev2: A => ￢[A] = { a: A => aEqBAndNotA.implies(a)._2 }
      val notAEqNotA = byContradiction { aEqNotA: A <=> ￢[A] =>
        val notA = byContradiction { a: A => a ∧ aEqNotA.implies(a) }
        val a: A = aEqNotA.impliedBy(notA)
        a ∧ notA
      }
      notAEqNotA(ev2 ∧ ev1)
    }
  
    byContradiction { assumption: ∃[[x <: Σ] => ∀[[y <: Σ] => y ∈ x]] =>
      type S = assumption.S
      val setOfAllSets = assumption.value

      val paradoxicalExistence: ∃[[z <: Σ] => ∀[[u <: Σ] => (u ∈ z) <=> ((u ∈ S) ∧ (u ∉ u))]] = 
        forType[S].instantiate[[p <: Σ] => ∃[[y <: Σ] => ∀[[u <: Σ] => (u ∈ y) <=> ((u ∈ S) ∧ (u ∉ u))]]](
          forType[S].instantiate[[x <: Σ] => ∀[[p <: Σ] => ∃[[y <: Σ] => ∀[[u <: Σ] => (u ∈ y) <=> ((u ∈ x) ∧ (u ∉ u))]]]](
            separation[[X <: Σ, _] => X ∉ X]
          )
        )
      type Z = paradoxicalExistence.S
      val paradoxicalSet: ∀[[u <: Σ] => (u ∈ Z) <=> ((u ∈ S) ∧ (u ∉ u))] = paradoxicalExistence.value
      val ev1: (Z ∈ Z) <=> ((Z ∈ S) ∧ (Z ∉ Z)) = forType[Z].instantiate[[u <: Σ] => (u ∈ Z) <=> ((u ∈ S) ∧ (u ∉ u))](paradoxicalSet)
      val ev2: Z ∈ S = forType[Z].instantiate[[y <: Σ] => y ∈ S](setOfAllSets)
      lemma1(ev1 ∧ ev2)
    }
  }

  /**
   * There exists a set containing all subsets of x and nothing else.
   */
  def existsPower(implicit axiom: ZFAxiom): ∀[[x <: Σ] => ∃[[y <: Σ] => y isPowerOf x]] = {
    byContradiction { assumption: ∃[[x <: Σ] => ￢[∃[[y <: Σ] => y isPowerOf x]]] =>
      // X is a 'base' set
      type X = assumption.S
      val ev1: ￢[∃[[y <: Σ] => y isPowerOf X]] = assumption.value
      val ev2: ∃[[y <: Σ] => ∀[[z <: Σ] => (z ⊂ X) => (z ∈ y)]] = forType[X].instantiate[[x <: Σ] => ∃[[p <: Σ] => ∀[[z <: Σ] => (z ⊂ x) => (z ∈ p)]]](power)

      // Y is a set containing power set of X
      type Y = ev2.S
      val ev3: ∀[[z <: Σ] => (z ⊂ X) => (z ∈ Y)] = ev2.value
      val ev4: ∃[[w <: Σ] => ∀[[u <: Σ] => (u ∈ w) <=> ((u ∈ Y) ∧ (u ⊂ X))]] =
        forType[X].instantiate[[p <: Σ] => ∃[[y <: Σ] => ∀[[u <: Σ] => (u ∈ y) <=> ((u ∈ Y) ∧ (u ⊂ p))]]](
          forType[Y].instantiate[[x <: Σ] => ∀[[p <: Σ] => ∃[[y <: Σ] => ∀[[u <: Σ] => (u ∈ y) <=> ((u ∈ x) ∧ (u ⊂ p))]]]](
            separation[[u <: Σ, p <: Σ] => u ⊂ p]
          )
        )

      // W is a power set of X
      type W = ev4.S
      val ev5: ∀[[z <: Σ] => (z ∈ W) <=> ((z ∈ Y) ∧ (z ⊂ X))] = ev4.value
      val ev6: ∀[[z <: Σ] => (z ∈ W) <=> (z ⊂ X)] = byContradiction { assumption6: ∃[[z <: Σ] => ￢[(z ∈ W) <=> (z ⊂ X)]] =>
        type Z = assumption6.S
        val ev61: ￢[(Z ∈ W) <=> (Z ⊂ X)] = assumption6.value
        val ev62: (Z ∈ W) <=> ((Z ∈ Y) ∧ (Z ⊂ X)) = forType[Z].instantiate[[z <: Σ] => (z ∈ W) <=> ((z ∈ Y) ∧ (z ⊂ X))](ev5)
        val ev63: (Z ⊂ X) => (Z ∈ Y) = forType[Z].instantiate[[z <: Σ] => (z ⊂ X) => (z ∈ Y)](ev3)
        val ev64: (Z ∈ W) => (Z ⊂ X) = ev62.implies.andThen(_._2)
        val ev65: (Z ⊂ X) => (Z ∈ W) = { zInX => ev62.impliedBy(ev63(zInX) ∧ zInX) }
        val ev66: (Z ∈ W) <=> (Z ⊂ X) = ev64 ∧ ev65
        ev66 ∧ ev61
      }
      val ev7: W isPowerOf X = ev6
      val ev8: ∃[[y <: Σ] => y isPowerOf X] = forType[W].generalize(ev7)
      ev8 ∧ ev1
    }
  }
}