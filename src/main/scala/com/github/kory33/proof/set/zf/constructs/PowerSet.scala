package com.github.kory33.proof.set.zf.constructs

import scala.language.implicitConversions

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.logic.propositional.ClassicalLogicSystem._
import com.github.kory33.proof.set.axiom.zf._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateSystem._
import com.github.kory33.proof.set.logic.Equality._
import com.github.kory33.proof.set.zf.Lemma._
import com.github.kory33.proof.set.zf.Lemma.Predicate
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set._

class PowerSetConstruct(implicit axiom: ZFExtensionality & ZFSeparation & ZFPower) {

  val existence: ∀[[x <: Σ] => ∃[[y <: Σ] => y isPowerOf x]] = {
    byContradiction { assumption: ∃[[x <: Σ] => ￢[∃[[y <: Σ] => y isPowerOf x]]] =>
      type X = assumption.S
      val ev1: ￢[∃[[y <: Σ] => y isPowerOf X]] = assumption.value
      val ev2: ∃[[y <: Σ] => ∀[[z <: Σ] => (z ⊂ X) => (z ∈ y)]] = forType[X].instantiate[[x <: Σ] => ∃[[p <: Σ] => ∀[[z <: Σ] => (z ⊂ x) => (z ∈ p)]]](axiom.power)
      val ev3: ∃[[y <: Σ] => ∀[[z <: Σ] => (z ∈ y) <=> (z ⊂ X)]] = comprehendsExactly[[z <: Σ] => z ⊂ X](ev2)
      val ev4: ∃[[y <: Σ] => y isPowerOf X] = ev3
      ev4 ∧ ev1
    }
  }

  val uniqueness: ∀[[z <: Σ] => ∀[[x <: Σ] => ∀[[y <: Σ] => (x isPowerOf z) ∧ (y isPowerOf z) => x =::= y]]] = {
    byContradiction { assumption: ∃[[z <: Σ] => ￢[∀[[x <: Σ] => ∀[[y <: Σ] => (x isPowerOf z) ∧ (y isPowerOf z) => x =::= y]]]] =>
      type Z = assumption.S
      val ev1: ∃[[x <: Σ] => ￢[∀[[y <: Σ] => (x isPowerOf Z) ∧ (y isPowerOf Z) => x =::= y]]] = assumption.value
      type X = ev1.S
      val ev2: ∃[[y <: Σ] => ￢[(X isPowerOf Z) ∧ (y isPowerOf Z) => X =::= y]] = ev1.value
      type Y = ev2.S
      val ev3: ￢[(X isPowerOf Z) ∧ (Y isPowerOf Z) => X =::= Y] = ev2.value
      val ev4: (X isPowerOf Z) ∧ (Y isPowerOf Z) => X =::= Y = equivalence[X, Y, [z <: Σ] => z ⊂ Z]
      ev4 ∧ ev3
    }
  }

  val powerFunctionExistence: ∃~>[[Pow[_ <: Σ] <: Σ] => ∀[[x <: Σ] => Pow[x] isPowerOf x]] = {
    createUnaryClassFunction[isPowerOf](uniqueExistence[isPowerOf](existence, uniqueness))
  }

  type Pow[x <: Σ] = powerFunctionExistence.F[x]
  val constraint: ∀[[x <: Σ] => Pow[x] isPowerOf x] = powerFunctionExistence.value
}
