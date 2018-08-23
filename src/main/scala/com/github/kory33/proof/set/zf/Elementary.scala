package com.github.kory33.proof.set.zf

import scala.language.implicitConversions

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.logic.propositional.ClassicalLogicSystem._
import com.github.kory33.proof.set.axiom.ZFAxiom
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateSystem._
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set._

import com.github.kory33.proof.set.zf.constructs._

class ElementaryConstructs(implicit axiom: ZFAxiom) {

  val comprehension = new ComprehensionConstruct

  val emptySet = new EmptySetConstruct
  type ∅ = emptySet.∅

  val pairSet = new PairSetConstruct
  type ++:[x <: Σ, y <: Σ] = pairSet.++:[x, y]

  val unionSet = new UnionSetConstruct
  type Union[F <: Σ] = unionSet.Union[F]

  val powerSet = new PowerSetConstruct
  type Pow[x <: Σ] = powerSet.Pow[x]

  val singleton = new SingletonConstruct(pairSet)
  type Just[x <: Σ] = singleton.Just[x]

  val binaryUnion = new BinaryUnionConstruct(pairSet, unionSet)
  type ∪[x <: Σ, y <: Σ] = binaryUnion.∪[x, y]

  val intersection = new IntersectionConstruct(comprehension, unionSet)
  type Intersection[F <: Σ] = intersection.Intersection[F]

  val binaryIntersection = new BinaryIntersectionConstruct(pairSet, intersection)
  type ∩[x <: Σ, y <: Σ] = binaryIntersection.∩[x, y]

  val orderedPair = new OrderedPairConstruct(singleton)
  type :::[a <: Σ, b <: Σ] = orderedPair.:::[a, b]

  val difference = new DifferenceConstruct(comprehension)
  type \[a <: Σ, b <: Σ] = difference.\[a, b]

  val symmetricDifference = new SymmetricDifferenceConstruct(difference, binaryUnion)
  type Δ[a <: Σ, b <: Σ] = symmetricDifference.Δ

  val cartesianProduct = new CartesianProductConstruct(comprehension, powerSet, binaryUnion, orderedPair)
  type ×[a <: Σ, b <: Σ] = cartesianProduct.×

}

class ElementaryTheorems(implicit axiom: ZFAxiom) {

  /**
   * There is no set of all sets.
   */
  val noSetOfAllSets: ￢[∃[[x <: Σ] => ∀[[y <: Σ] => y ∈ x]]] = {
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
      import Lemma._

      type S = assumption.S
      val setOfAllSets = assumption.value

      val paradoxicalExistence: ∃[[z <: Σ] => ∀[[u <: Σ] => (u ∈ z) <=> ((u ∈ S) ∧ (u ∉ u))]] = separate[S, [X <: Σ] => X ∉ X]
      type Z = paradoxicalExistence.S
      val paradoxicalSet: ∀[[u <: Σ] => (u ∈ Z) <=> ((u ∈ S) ∧ (u ∉ u))] = paradoxicalExistence.value
      val ev1: (Z ∈ Z) <=> ((Z ∈ S) ∧ (Z ∉ Z)) = forType[Z].instantiate[[u <: Σ] => (u ∈ Z) <=> ((u ∈ S) ∧ (u ∉ u))](paradoxicalSet)
      val ev2: Z ∈ S = forType[Z].instantiate[[y <: Σ] => y ∈ S](setOfAllSets)
      lemma1(ev1 ∧ ev2)
    }
  }

}
