package com.github.kory33.proof.set

import scala.language.implicitConversions

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateSystem._
import com.github.kory33.proof.set.logic._
import com.github.kory33.proof.set.logic.Equality._
import com.github.kory33.proof.set.SetDefinitions._

/**
 * Theorems that do not depend on choice of axiom systems
 */
object Universal {
  implicit def selfInclusion[A <: Σ]: A ⊂ A = {
    byContradiction { assumption: ∃[[z <: Σ] => ￢[(z ∈ A) => (z ∈ A)]] =>
      type Z = assumption.S
      val ev1: ￢[(Z ∈ A) => (Z ∈ A)] = assumption.value
      val ev2: (Z ∈ A) => (Z ∈ A) = identity
      ev2 ∧ ev1
    }
  }

  implicit def inclusion[A <: Σ, B <: Σ](ev: A =::= B): A ⊂ B = {
    val ev1: A ⊂ A = implicitly
    val ev2: A ⊂ B = ev.sub[[b <: Σ] => A ⊂ b](ev1)
    ev2
  }

  implicit class SubsetRelation[A <: Σ, B <: Σ](ev: A ⊂ B) {
    def containsElement[x <: Σ](xInA: x ∈ A): x ∈ B = forType[x].instantiate[[z <: Σ] => (z ∈ A) => (z ∈ B)](ev)(xInA)
  }
}
