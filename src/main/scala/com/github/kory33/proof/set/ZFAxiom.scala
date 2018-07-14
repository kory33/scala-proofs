package com.github.kory33.proof.set

import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
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
  def existence: ∃[[x <: AxiomaticSet] => x =#= x]

  /**
    * Axiom of extensionality.
    *
    * For all set x and y, x contains and is contained in y when they have exactly same elements.
    */
  def extensionality: ∀[[x <: AxiomaticSet] => ∀[[y <: AxiomaticSet] => ∀[[z <: AxiomaticSet] => (z ∈ x) <=> (z ∈ y)] <=> (x =#= y)]]

  /**
    * Schema of separation.
    *
    * For every binary predicate F of free variables,
    * every set x and parameter p, there exists set y = { u ∈ x | F(u, p) }.
    *
    * @tparam F binary predicate
    */
  def separation[F[_ <: AxiomaticSet, _ <: AxiomaticSet]]: ∀[[x <: AxiomaticSet] => ∀[[p <: AxiomaticSet] => ∃[[y <: AxiomaticSet] => ∀[[u <: AxiomaticSet] => (u ∈ y) <=> ((u ∈ x) ∧ F[u, p])]]]]

  /**
    * Axiom of pairing
    *
    * For any a and b there exists x that contains a and b.
    */
  def pairing: ∀[[a <: AxiomaticSet] => ∀[[b <: AxiomaticSet] => ∃[[x <: AxiomaticSet] => (a ∈ x) ∧ (b ∈ x)]]]

  /**
    * Axiom of union.
    *
    * For every family F there exists a set U containing all elements of F.
    */
  def union: ∀[[F <: AxiomaticSet] => ∃[[u <: AxiomaticSet] => ∀[[y <: AxiomaticSet] => ∀[[x <: AxiomaticSet] => ((x ∈ y) ∧ (y ∈ F)) => x ∈ u]]]]

  /**
    * Axiom of power set.
    *
    * For every set x there exists a set P containing all subsets of x.
    */
  def power: ∀[[x <: AxiomaticSet] => ∃[[p <: AxiomaticSet] => ∀[[z <: AxiomaticSet] => (z ⊂ x) => (z ∈ p)]]]

  /**
   * Axiom of Infinity.
   *
   * There exists an infinite set of some special form.
   */
  def infinity: ∃[[x <: AxiomaticSet] => ∀[[z <: AxiomaticSet] => isEmpty[z] => (z ∈ x)] ∧ (x hasAll ([y <: AxiomaticSet] => ∀[[z <: AxiomaticSet] => (z isSucc y) => (z ∈ x)]))]

  /**
   * Axiom schema of replacement.
   *
   * For every formula φ, A and p, if φ(s, t, A, p) defines a function F on A by F(x) = y ⇔ φ(x, y, A, p)
   * then there exists a set Y containing the range F[A] = {F(x): x ∈ A} of the function F.
   */
  def replacement[φ[_ <: AxiomaticSet, _ <: AxiomaticSet, _ <: AxiomaticSet, _ <: AxiomaticSet]]: ∀[[A <: AxiomaticSet] => ∀[[p <: AxiomaticSet] => A hasAll ([x <: AxiomaticSet] => ∃![[y <: AxiomaticSet] => φ[x, y, A, p]]) => ∃[[Y <: AxiomaticSet] => A hasAll ([x <: AxiomaticSet] => Y hasSome ([y <: AxiomaticSet] => φ[x, y, A, p]))]]]

  /**
   * Axiom of foundation / regularity.
   * Every nonempty set has an ∈-minimal element.
   */
  def foundation: ∀[[x <: AxiomaticSet] => isNonEmpty[x] => x hasSome ([y <: AxiomaticSet] => x isDisjointTo y)]

}

object ZFAxiom {
  def existence(implicit axiom: ZFAxiom): ∃[[x <: AxiomaticSet] => x =#= x]
    = axiom.existence
  def extensionality(implicit axiom: ZFAxiom): ∀[[x <: AxiomaticSet] => ∀[[y <: AxiomaticSet] => ∀[[z <: AxiomaticSet] => (z ∈ x) <=> (z ∈ y)] <=> (x =#= y)]]
    = axiom.extensionality
  def separation[F[_ <: AxiomaticSet, _ <: AxiomaticSet]](implicit axiom: ZFAxiom): ∀[[x <: AxiomaticSet] => ∀[[p <: AxiomaticSet] => ∃[[y <: AxiomaticSet] => ∀[[u <: AxiomaticSet] => (u ∈ y) <=> ((u ∈ x) ∧ F[u, p])]]]]
    = axiom.separation
  def pairing(implicit axiom: ZFAxiom): ∀[[a <: AxiomaticSet] => ∀[[b <: AxiomaticSet] => ∃[[x <: AxiomaticSet] => (a ∈ x) ∧ (b ∈ x)]]]
    = axiom.pairing
  def union(implicit axiom: ZFAxiom): ∀[[F <: AxiomaticSet] => ∃[[u <: AxiomaticSet] => ∀[[y <: AxiomaticSet] => ∀[[x <: AxiomaticSet] => ((x ∈ y) ∧ (y ∈ F)) => x ∈ u]]]]
    = axiom.union
  def power(implicit axiom: ZFAxiom): ∀[[x <: AxiomaticSet] => ∃[[p <: AxiomaticSet] => ∀[[z <: AxiomaticSet] => (z ⊂ x) => (z ∈ p)]]]
    = axiom.power
  def infinity(implicit axiom: ZFAxiom): ∃[[x <: AxiomaticSet] => ∀[[z <: AxiomaticSet] => isEmpty[z] => (z ∈ x)] ∧ (x hasAll ([y <: AxiomaticSet] => ∀[[z <: AxiomaticSet] => (z isSucc y) => (z ∈ x)]))]
    = axiom.infinity
  def replacement[φ[_ <: AxiomaticSet, _ <: AxiomaticSet, _ <: AxiomaticSet, _ <: AxiomaticSet]](implicit axiom: ZFAxiom): ∀[[A <: AxiomaticSet] => ∀[[p <: AxiomaticSet] => A hasAll ([x <: AxiomaticSet] => ∃![[y <: AxiomaticSet] => φ[x, y, A, p]]) => ∃[[Y <: AxiomaticSet] => A hasAll ([x <: AxiomaticSet] => Y hasSome ([y <: AxiomaticSet] => φ[x, y, A, p]))]]]
    = axiom.replacement
  def foundation(implicit axiom: ZFAxiom): ∀[[x <: AxiomaticSet] => isNonEmpty[x] => x hasSome ([y <: AxiomaticSet] => x isDisjointTo y)]
    = axiom.foundation
}