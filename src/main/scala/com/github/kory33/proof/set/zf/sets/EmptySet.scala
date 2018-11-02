package com.github.kory33.proof.set.zf.sets

import scala.language.implicitConversions

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.logic.propositional.ClassicalLogicSystem._
import com.github.kory33.proof.set.axiom.zf._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateSystem._
import com.github.kory33.proof.logic.predicate.Equality._
import com.github.kory33.proof.set.zf.Lemma._
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set._

class EmptySet(implicit axiom: ZFExistence & ZFExtensionality & ZFSeparation) {

  /**
    * There exists an empty set.
    */
  implicit val existence: ∃[isEmpty] = {
    implicit val set = existence

    type Set = set.S

    implicit val emptyExistence: ∃[[y] => ∀[[u] => (u ∈ y) <=> ((u ∈ Set) ∧ Nothing)]] = separate[Set, [_] => Nothing]

    type EmptySet = emptyExistence.S
    val ev1: ∀[[u] => (u ∈ EmptySet) <=> ((u ∈ Set) ∧ Nothing)] = emptyExistence.instance
    val ev2: ∀[[u] => (u ∈ EmptySet) => Nothing] = byContradiction { implicit assumption: ∃[[u] => ￢[u ∈ EmptySet] => Nothing] =>
      type U = assumption.S
      val ev21 = assumption.instance
      val ev22 = forType[U].instantiate[[u] => (u ∈ EmptySet) <=> ((u ∈ Set) ∧ Nothing)](ev1)
      val ev23 = ev22.implies.andThen { conclusion: (U ∈ Set) ∧ Nothing => conclusion._2 }
      ev21(ev23)
    }
    val ev3: ∀[[u] => u ∉ EmptySet] = ev2
  
    forType[EmptySet].generalize[[x] => ∀[[y] => y ∉ x]](ev3)
  }

  type ∅ = existence.S
  val constraint: isEmpty[∅] = existence.instance

  val uniqueness: ∀[[x] => isEmpty[x] => (x =::= ∅)] = {
    byContradiction { implicit assumption: ∃[[x] => ￢[isEmpty[x] => (x =::= ∅)]] =>
      type X = assumption.S
      val ev1: ￢[isEmpty[X] => (X =::= ∅)] = assumption.instance
      val ev2: ∀[[z] => (z ∈ X) <=> (z ∈ ∅)] => (X =::= ∅) = {
        forType2[X, ∅].instantiate[[x, y] => ∀[[z] => (z ∈ x) <=> (z ∈ y)] => (x =::= y)](axiom.extensionality)
      }
      val ev3: isEmpty[X] => ∀[[z] => (z ∈ X) <=> (z ∈ ∅)] = { xIsEmpty: ∀[[y] => y ∉ X] =>
        byContradiction { implicit assumption3: ∃[[z] => ￢[(z ∈ X) <=> (z ∈ ∅)]] =>
          type Z = assumption3.S
          val ev31: ￢[(Z ∈ X) <=> (Z ∈ ∅)] = assumption3.instance
          val ev32: (Z ∈ X) => (Z ∈ ∅) = { assumption32: Z ∈ X =>
            assumption32 ∧ forType[Z].instantiate[[y] => y ∉ X](xIsEmpty)
          }
          val ev33: (Z ∈ ∅) => (Z ∈ X) = { assumption33: Z ∈ ∅ =>
            assumption33 ∧ forType[Z].instantiate[[y] => y ∉ ∅](existence.instance)
          }
          val ev34: (Z ∈ X) <=> (Z ∈ ∅) = ev32 ∧ ev33
          ev34 ∧ ev31
        }
      }
      val ev4: isEmpty[X] => (X =::= ∅) = ev3.andThen(ev2)
      ev4 ∧ ev1
    }
  }
}
