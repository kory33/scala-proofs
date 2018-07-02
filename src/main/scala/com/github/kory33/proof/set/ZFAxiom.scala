package com.github.kory33.proof.set

import com.github.kory33.proof.logic.predicate.PredicateLogicDefinitions.{∃, _}
import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.set.SetDefinitions.{∈, _}

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
  /*
  def empty:
    ∃[({ type λ1[x] =
      ∀[({ type λ2[y] =
        y ∈ x => y =/= y
      })#λ2]
    })#λ1] = {
    val separated = separation[({ type λ[u, _] = u =/= u })#λ]

    // all x has prop F(x), there exists some y such that G(y). then there exists some y such that F(x) && G(y).

  }
  */
}
