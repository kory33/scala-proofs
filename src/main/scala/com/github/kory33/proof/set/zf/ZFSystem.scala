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

import com.github.kory33.proof.set.zf.operators._
import com.github.kory33.proof.set.zf.sets._

class ZFSystem(implicit axiom: ZFAxiom) {

  val comprehension = new ComprehensionConstruct

  val emptySet = new EmptySet
  type ∅ = emptySet.∅

  val pairSet = new PairSetConstruct
  type ++:[x, y] = pairSet.++:[x, y]

  val unionSet = new UnionSetConstruct
  type Union[F] = unionSet.Union[F]

  val powerSet = new PowerSetConstruct
  type Pow[x] = powerSet.Pow[x]

  val singleton = new SingletonConstruct(pairSet)
  type Just[x] = singleton.Just[x]

  val binaryUnion = new BinaryUnionConstruct(pairSet, unionSet)
  type ∪[x, y] = binaryUnion.∪[x, y]

  val intersection = new IntersectionConstruct(comprehension, unionSet)
  type Intersection[F] = intersection.Intersection[F]

  val binaryIntersection = new BinaryIntersectionConstruct(pairSet, intersection)
  type ∩[x, y] = binaryIntersection.∩[x, y]

  val orderedPair = new OrderedPairConstruct(singleton)
  type :::[a, b] = orderedPair.:::[a, b]

  val difference = new DifferenceConstruct(comprehension)
  type \[a, b] = difference.\[a, b]

  val symmetricDifference = new SymmetricDifferenceConstruct(difference, binaryUnion)
  type Δ[a, b] = symmetricDifference.Δ[a, b]

  val cartesianProduct = new CartesianProductConstruct(comprehension, powerSet, binaryUnion, orderedPair)
  type ×[a, b] = cartesianProduct.×[a, b]

}

class ElementaryTheorems(implicit axiom: ZFAxiom) {

  /**
   * There is no set of all sets.
   */
  val noSetOfAllSets: ￢[∃[[x] => ∀[[y] => y ∈ x]]] = {
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
  
    byContradiction { implicit assumption: ∃[[x] => ∀[[y] => y ∈ x]] =>
      import Lemma._

      type S = assumption.S
      val setOfAllSets = assumption.instance

      implicit val paradoxicalExistence: ∃[[z] => ∀[[u] => (u ∈ z) <=> ((u ∈ S) ∧ (u ∉ u))]] = separate[S, [X] => X ∉ X]
      type Z = paradoxicalExistence.S
      val paradoxicalSet: ∀[[u] => (u ∈ Z) <=> ((u ∈ S) ∧ (u ∉ u))] = paradoxicalExistence.instance
      val ev1: (Z ∈ Z) <=> ((Z ∈ S) ∧ (Z ∉ Z)) = forType[Z].instantiate[[u] => (u ∈ Z) <=> ((u ∈ S) ∧ (u ∉ u))](paradoxicalSet)
      val ev2: Z ∈ S = forType[Z].instantiate[[y] => y ∈ S](setOfAllSets)
      lemma1(ev1 ∧ ev2)
    }
  }

}
