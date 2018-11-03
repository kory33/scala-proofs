package com.github.kory33.proof.set

import scala.language.implicitConversions

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.logic.predicate.Equality._
import com.github.kory33.proof.set.logic.SetDomain
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateSystem._
import com.github.kory33.proof.set.SetDefinitions._

/**
 * Theorems that do not depend on choice of axiom systems
 */
object Universal {
  /**
   * "isElementOf" relation is a meta-logical relation defined on sets
   */
  implicit def elementRelationOnSetsLeft[x, y](implicit ev: x ∈ y): SetDomain[x] = ev.xSetDomain
  implicit def elementRelationOnSetsRight[x, y](implicit ev: x ∈ y): SetDomain[y] = ev.ySetDomain

  implicit def selfInclusion[A]: A ⊂ A = {
    byContradiction { implicit assumption: ∃[[z] => ￢[(z ∈ A) => (z ∈ A)]] =>
      type Z = assumption.S
      val ev1: ￢[(Z ∈ A) => (Z ∈ A)] = assumption.instance
      val ev2: (Z ∈ A) => (Z ∈ A) = identity
      ev2 ∧ ev1
    }
  }

  implicit def inclusion[A, B](ev: A =::= B): A ⊂ B = {
    val ev1: A ⊂ A = implicitly
    val ev2: A ⊂ B = ev.sub[[b] => A ⊂ b](ev1)
    ev2
  }

  implicit class SubsetRelation[A, B](ev: A ⊂ B) {
    def containsElement[x : SetDomain](xInA: x ∈ A): x ∈ B = {
      forType[x].instantiate[[z] => (z ∈ A) => (z ∈ B)](ev)(xInA)
    }
  }

}
