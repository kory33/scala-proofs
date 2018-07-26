package com.github.kory33.proof.set

import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.logic.predicate.PredicateLogicSystem._
import com.github.kory33.proof.logic.predicate._
import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.set.SetDefinitions._

trait ZFAxiom {

  /**
    * Axiom of existence.
    *
    * There exists a set.
    */
  def existence: ∃[[x <: Σ] => x =::= x]

  /**
    * Axiom of extensionality.
    *
    * For all set x and y, x contains and is contained in y when they have exactly same elements.
    */
  def extensionality: ∀[[x <: Σ] => ∀[[y <: Σ] => ∀[[z <: Σ] => (z ∈ x) <=> (z ∈ y)] => (x =::= y)]]

  /**
    * Schema of separation.
    *
    * For every binary predicate F of free variables,
    * every set x and parameter p, there exists set y = { u ∈ x | F(u, p) }.
    *
    * @tparam F binary predicate
    */
  def separation[F[_ <: Σ, _ <: Σ]]: ∀[[x <: Σ] => ∀[[p <: Σ] => ∃[[y <: Σ] => ∀[[u <: Σ] => (u ∈ y) <=> ((u ∈ x) ∧ F[u, p])]]]]

  /**
    * Axiom of pairing
    *
    * For any a and b there exists x that contains a and b.
    */
  def pairing: ∀[[a <: Σ] => ∀[[b <: Σ] => ∃[[x <: Σ] => (a ∈ x) ∧ (b ∈ x)]]]

  /**
    * Axiom of union.
    *
    * For every family F there exists a set U containing all elements of F.
    */
  def union: ∀[[F <: Σ] => ∃[[u <: Σ] => ∀[[y <: Σ] => ∀[[x <: Σ] => ((x ∈ y) ∧ (y ∈ F)) => x ∈ u]]]]

  /**
    * Axiom of power set.
    *
    * For every set x there exists a set P containing all subsets of x.
    */
  def power: ∀[[x <: Σ] => ∃[[p <: Σ] => ∀[[z <: Σ] => (z ⊂ x) => (z ∈ p)]]]

  /**
   * Axiom of Infinity.
   *
   * There exists an infinite set of some special form.
   */
  def infinity: ∃[[x <: Σ] => ∀[[z <: Σ] => isEmpty[z] => (z ∈ x)] ∧ (x hasAll ([y <: Σ] => ∀[[z <: Σ] => (z isSucc y) => (z ∈ x)]))]

  /**
   * Axiom schema of replacement.
   *
   * For every formula φ, A and p, if φ(s, t, A, p) defines a function F on A by F(x) = y ⇔ φ(x, y, A, p)
   * then there exists a set Y containing the range F[A] = {F(x): x ∈ A} of the function F.
   */
  def replacement[φ[_ <: Σ, _ <: Σ, _ <: Σ, _ <: Σ]]: ∀[[A <: Σ] => ∀[[p <: Σ] => A hasAll ([x <: Σ] => ∃![[y <: Σ] => φ[x, y, A, p]]) => ∃[[Y <: Σ] => A hasAll ([x <: Σ] => Y hasSome ([y <: Σ] => φ[x, y, A, p]))]]]

  /**
   * Axiom of foundation / regularity.
   * Every nonempty set has an ∈-minimal element.
   */
  def foundation: ∀[[x <: Σ] => isNonEmpty[x] => x hasSome ([y <: Σ] => x isDisjointTo y)]

}

object ZFAxiom {
  def existence(implicit axiom: ZFAxiom): ∃[[x <: Σ] => x =::= x]
    = axiom.existence
  def extensionality(implicit axiom: ZFAxiom): ∀[[x <: Σ] => ∀[[y <: Σ] => ∀[[z <: Σ] => (z ∈ x) <=> (z ∈ y)] => (x =::= y)]]
    = axiom.extensionality
  def separation[F[_ <: Σ, _ <: Σ]](implicit axiom: ZFAxiom): ∀[[x <: Σ] => ∀[[p <: Σ] => ∃[[y <: Σ] => ∀[[u <: Σ] => (u ∈ y) <=> ((u ∈ x) ∧ F[u, p])]]]]
    = axiom.separation
  def pairing(implicit axiom: ZFAxiom): ∀[[a <: Σ] => ∀[[b <: Σ] => ∃[[x <: Σ] => (a ∈ x) ∧ (b ∈ x)]]]
    = axiom.pairing
  def union(implicit axiom: ZFAxiom): ∀[[F <: Σ] => ∃[[u <: Σ] => ∀[[y <: Σ] => ∀[[x <: Σ] => ((x ∈ y) ∧ (y ∈ F)) => x ∈ u]]]]
    = axiom.union
  def power(implicit axiom: ZFAxiom): ∀[[x <: Σ] => ∃[[p <: Σ] => ∀[[z <: Σ] => (z ⊂ x) => (z ∈ p)]]]
    = axiom.power
  def infinity(implicit axiom: ZFAxiom): ∃[[x <: Σ] => ∀[[z <: Σ] => isEmpty[z] => (z ∈ x)] ∧ (x hasAll ([y <: Σ] => ∀[[z <: Σ] => (z isSucc y) => (z ∈ x)]))]
    = axiom.infinity
  def replacement[φ[_ <: Σ, _ <: Σ, _ <: Σ, _ <: Σ]](implicit axiom: ZFAxiom): ∀[[A <: Σ] => ∀[[p <: Σ] => A hasAll ([x <: Σ] => ∃![[y <: Σ] => φ[x, y, A, p]]) => ∃[[Y <: Σ] => A hasAll ([x <: Σ] => Y hasSome ([y <: Σ] => φ[x, y, A, p]))]]]
    = axiom.replacement
  def foundation(implicit axiom: ZFAxiom): ∀[[x <: Σ] => isNonEmpty[x] => x hasSome ([y <: Σ] => x isDisjointTo y)]
    = axiom.foundation
}