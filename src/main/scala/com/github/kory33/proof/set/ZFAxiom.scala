package com.github.kory33.proof.set

import com.github.kory33.proof.logic.predicate.PredicateLogicDefinitions.{∃, _}
import com.github.kory33.proof.logic.propositional.ClassicalLogicAxiom
import com.github.kory33.proof.logic.predicate.PredicateLogicSystem._
import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.set.SetDefinitions._

trait ZFAxiom {

  /**
    * Axiom of existence.
    *
    * There exists a set.
    */
  def existence: ∃[[x] => x =#= x]

  /**
    * Axiom of extensionality.
    *
    * For all set x and y, x contains and is contained in y when they have exactly same elements.
    */
  def extensionality: ∀[[x] => ∀[[y] => ∀[[z] => (z ∈ x) ≣ (z ∈ y)] => x =#= y]]

  /**
    * Schema of separation.
    *
    * For every binary predicate F of free variables,
    * every set x and parameter p, there exists set y = { u ∈ x | F(u, p) }.
    *
    * @tparam F binary predicate
    */
  def separation[F[_, _]]: ∀[[x] => ∀[[p] => ∃[[y] => ∀[[u] => (u ∈ y) ≣ ((u ∈ x) ∧ F[u, p])]]]]

  /**
    * Axiom of pairing
    *
    * For any a and b there exists x that contains a and b.
    */
  def pairing: ∀[[a] => ∀[[b] => ∃[[x] => (a ∈ x) ∧ (a ∈ x)]]]

  /**
    * Axiom of union.
    *
    * For every family F there exists a set U containing all elements of F.
    */
  def union[F <: Family]: ∃[[U] => ∀[[Y] => ∀[[x] => ((x ∈ Y) ∧ (Y ∈ F)) => x ∈ U]]]

  /**
    * Axiom of power set.
    *
    * For every set x there exists a set P containing all subsets of x.
    */
  def power: ∀[[X] => ∃[[P] => ∀[[z] => (z ⊂ X) => (z ∈ P)]]]

  /**
    * Axiom of empty set.
    *
    * There exists an empty set.
    *
    * This is actually not in axiom set and is deduced from other axioms
    */
  def existsEmpty(implicit predAxiom: ClassicalLogicAxiom): ∃[[x] => ∀[[y] => y ∉ x]] = {
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
}
