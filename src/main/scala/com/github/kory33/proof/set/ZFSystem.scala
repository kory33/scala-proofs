package com.github.kory33.proof.set

import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateSystem._
import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set.ZFAxiom._

object ZFSystem {
  /**
   * shorthand for axiom schema of separation.
   */
  def separate[X <: Σ, F[_ <: Σ, _ <: Σ], A <: Σ](implicit axiom: ZFAxiom): ∃[[y <: Σ] => ∀[[u <: Σ] => (u ∈ y) <=> ((u ∈ X) ∧ F[u, A])]] =
    forType[A].instantiate[[p <: Σ] => ∃[[y <: Σ] => ∀[[u <: Σ] => (u ∈ y) <=> ((u ∈ X) ∧ F[u, p])]]](
      forType[X].instantiate[[x <: Σ] => ∀[[p <: Σ] => ∃[[y <: Σ] => ∀[[u <: Σ] => (u ∈ y) <=> ((u ∈ x) ∧ F[u, p])]]]](
        separation[F]
      )
    )

  /**
   * If there exists a set containing all set u such that F[u], then there exists a subset containing all u such that F[u] and nothing else.
   */
  def comprehendsExactly[F[_ <: Σ]](existsSuperSet: ∃[[y <: Σ] => ∀[[z <: Σ] => F[z] => (z ∈ y)]])(implicit axiom: ZFAxiom): ∃[[y <: Σ] => ∀[[z <: Σ] => (z ∈ y) <=> F[z]]] = {
    type Y = existsSuperSet.S
    val ev1: ∀[[u <: Σ] => F[u] => (u ∈ Y)] = existsSuperSet.value
    val ev2: ∃[[w <: Σ] => ∀[[u <: Σ] => (u ∈ w) <=> ((u ∈ Y) ∧ F[u])]] = separate[Y, [u <: Σ, _ <: Σ] => F[u], Y]
    type W = ev2.S
    val ev3: ∀[[u <: Σ] => (u ∈ W) <=> ((u ∈ Y) ∧ F[u])] = ev2.value
    val ev4: ∀[[u <: Σ] => (u ∈ W) <=> F[u]] = byContradiction { assumption: ∃[[u <: Σ] => ￢[(u ∈ W) <=> F[u]]] =>
      type U = assumption.S
      val ev41: ￢[(U ∈ W) <=> F[U]] = assumption.value
      val ev42: (U ∈ W) <=> ((U ∈ Y) ∧ F[U]) = forType[U].instantiate[[u <: Σ] => (u ∈ W) <=> ((u ∈ Y) ∧ F[u])](ev3)
      val ev43: (U ∈ W) => F[U] = ev42.implies.andThen(_._2)
      val ev44: F[U] => (U ∈ Y) = forType[U].instantiate[[u <: Σ] => F[u] => (u ∈ Y)](ev1)
      val ev45: F[U] => (U ∈ W) = { fu: F[U] => ev42.impliedBy(ev44(fu) ∧ fu) }
      val ev46: (U ∈ W) <=> F[U] = ev43 ∧ ev45
      ev46 ∧ ev41
    }
    forType[W].generalize[[y <: Σ] => ∀[[z <: Σ] => (z ∈ y) <=> F[z]]](ev4)
  }

  /**
    * There exists an empty set.
    */
  def existsEmpty(implicit axiom: ZFAxiom): ∃[isEmpty] = {
    val set = existence

    type Set = set.S

    val emptyExistence: ∃[[y <: Σ] => ∀[[u <: Σ] => (u ∈ y) <=> ((u ∈ Set) ∧ Nothing)]] = separate[Set, [_, _] => Nothing, Set]

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

      val paradoxicalExistence: ∃[[z <: Σ] => ∀[[u <: Σ] => (u ∈ z) <=> ((u ∈ S) ∧ (u ∉ u))]] = separate[S, [X <: Σ, _] => X ∉ X, S]
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
      type X = assumption.S
      val ev1: ￢[∃[[y <: Σ] => y isPowerOf X]] = assumption.value
      val ev2: ∃[[y <: Σ] => ∀[[z <: Σ] => (z ⊂ X) => (z ∈ y)]] = forType[X].instantiate[[x <: Σ] => ∃[[p <: Σ] => ∀[[z <: Σ] => (z ⊂ x) => (z ∈ p)]]](power)
      val ev3: ∃[[y <: Σ] => ∀[[z <: Σ] => (z ∈ y) <=> (z ⊂ X)]] = comprehendsExactly[[z <: Σ] => z ⊂ X](ev2)
      val ev4: ∃[[y <: Σ] => y isPowerOf X] = ev3
      ev4 ∧ ev1
    }
  }
}