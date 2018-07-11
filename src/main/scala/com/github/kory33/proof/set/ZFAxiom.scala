package com.github.kory33.proof.set

import com.github.kory33.proof.logic.predicate.PredicateLogicDefinitions.{∃, _}
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
  def union: ∀[[F] => ∃[[u] => ∀[[y] => ∀[[x] => ((x ∈ y) ∧ (y ∈ F)) => x ∈ u]]]]

  /**
    * Axiom of power set.
    *
    * For every set x there exists a set P containing all subsets of x.
    */
  def power: ∀[[x] => ∃[[p] => ∀[[z] => (z ⊂ x) => (z ∈ p)]]]

}

object ZFAxiom {
  def existence(implicit axiom: ZFAxiom): ∃[[x] => x =#= x] = axiom.existence
  def extensionality(implicit axiom: ZFAxiom): ∀[[x] => ∀[[y] => ∀[[z] => (z ∈ x) ≣ (z ∈ y)] => x =#= y]] = axiom.extensionality
  def separation[F[_, _]](implicit axiom: ZFAxiom): ∀[[x] => ∀[[p] => ∃[[y] => ∀[[u] => (u ∈ y) ≣ ((u ∈ x) ∧ F[u, p])]]]] = axiom.separation
  def pairing(implicit axiom: ZFAxiom): ∀[[a] => ∀[[b] => ∃[[x] => (a ∈ x) ∧ (a ∈ x)]]] = axiom.pairing
  def union(implicit axiom: ZFAxiom): ∀[[F] => ∃[[u] => ∀[[y] => ∀[[x] => ((x ∈ y) ∧ (y ∈ F)) => x ∈ u]]]] = axiom.union
  def power(implicit axiom: ZFAxiom): ∀[[x] => ∃[[p] => ∀[[z] => (z ⊂ x) => (z ∈ p)]]] = axiom.power
}