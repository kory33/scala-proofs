package com.github.kory33.proof.set.zf.operators

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
    byContradiction { assumption: ￢[∀[[z <: Σ] => ∀[[x <: Σ] => ∀[[y <: Σ] => (x isPowerOf z) ∧ (y isPowerOf z) => x =::= y]]]] =>
      val ev1: ∃[[z <: Σ] => ∃[[x <: Σ] => ∃[[y <: Σ] => ￢[(x isPowerOf z) ∧ (y isPowerOf z) => x =::= y]]]] = {
        notForall3[[z <: Σ, x <: Σ, y <: Σ] => (x isPowerOf z) ∧ (y isPowerOf z) => x =::= y](assumption)
      }
      type Z = ev1.S; type X = ev1.value.S; type Y = ev1.value.value.S
      val ev2: ￢[(X isPowerOf Z) ∧ (Y isPowerOf Z) => X =::= Y] = ev1.value.value.value
      val ev3: (X isPowerOf Z) ∧ (Y isPowerOf Z) => X =::= Y = equivalence[X, Y, [z <: Σ] => z ⊂ Z]
      ev3 ∧ ev2
    }
  }

  val powerFunctionExistence: ∃~>[[Pow[_ <: Σ] <: Σ] => ∀[[x <: Σ] => Pow[x] isPowerOf x]] = {
    createUnaryClassFunction[isPowerOf](uniqueExistence[isPowerOf](existence, uniqueness))
  }

  type Pow[x <: Σ] = powerFunctionExistence.F[x]
  val constraintValue: ∀[[x <: Σ] => Pow[x] isPowerOf x] = powerFunctionExistence.value
  def constraint[x <: Σ, z <: Σ]: (z ∈ Pow[x]) <=> (z ⊂ x) = {
    forType[z].instantiate[[z <: Σ] => (z ∈ Pow[x]) <=> (z ⊂ x)](
      forType[x].instantiate[[x <: Σ] => Pow[x] isPowerOf x](constraintValue)
    )
  }

}
