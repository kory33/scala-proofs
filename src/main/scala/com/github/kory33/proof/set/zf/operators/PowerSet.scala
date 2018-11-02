package com.github.kory33.proof.set.zf.operators

import scala.language.implicitConversions

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.logic.propositional.ClassicalLogicSystem._
import com.github.kory33.proof.set.axiom.zf._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateSystem._
import com.github.kory33.proof.set.logic.SetDomain
import com.github.kory33.proof.logic.predicate.Equality._
import com.github.kory33.proof.set.zf.Lemma._
import com.github.kory33.proof.set.zf.Lemma.Predicate
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set._

class PowerSetConstruct(implicit axiom: ZFExtensionality & ZFSeparation & ZFPower) {

  val existence: ∀[[x] => ∃[[y] => y isPowerOf x]] = {
    byContradiction { implicit assumption: ∃[[x] => ￢[∃[[y] => y isPowerOf x]]] =>
      type X = assumption.S
      val ev1: ￢[∃[[y] => y isPowerOf X]] = assumption.instance
      val ev2: ∃[[y] => ∀[[z] => (z ⊂ X) => (z ∈ y)]] = forType[X].instantiate[[x] => ∃[[p] => ∀[[z] => (z ⊂ x) => (z ∈ p)]]](axiom.power)
      val ev3: ∃[[y] => ∀[[z] => (z ∈ y) <=> (z ⊂ X)]] = comprehendsExactly[[z] => z ⊂ X](ev2)
      val ev4: ∃[[y] => y isPowerOf X] = ev3
      ev4 ∧ ev1
    }
  }

  val uniqueness: ∀[[z] => ∀[[x] => ∀[[y] => (x isPowerOf z) ∧ (y isPowerOf z) => x =::= y]]] = {
    byContradiction { assumption: ￢[∀[[z] => ∀[[x] => ∀[[y] => (x isPowerOf z) ∧ (y isPowerOf z) => x =::= y]]]] =>
      implicit val ev1: ∃[[z] => ∃[[x] => ∃[[y] => ￢[(x isPowerOf z) ∧ (y isPowerOf z) => x =::= y]]]] = {
        notForall3[[z, x, y] => (x isPowerOf z) ∧ (y isPowerOf z) => x =::= y](assumption)
      }
      type Z = ev1.S
      implicit val ev11 = ev1.instance
      type X = ev11.S
      implicit val ev12 = ev11.instance
      type Y = ev12.S
      val ev2: ￢[(X isPowerOf Z) ∧ (Y isPowerOf Z) => X =::= Y] = ev12.instance
      val ev3: (X isPowerOf Z) ∧ (Y isPowerOf Z) => X =::= Y = equivalence[X, Y, [z] => z ⊂ Z]
      ev3 ∧ ev2
    }
  }

  val powerFunctionExistence: ∃~>[[Pow[_]] => ∀[[x] => Pow[x] isPowerOf x]] = {
    createUnaryClassFunction[isPowerOf](uniqueExistence[isPowerOf](existence, uniqueness))
  }

  type Pow[x] = powerFunctionExistence.F[x]
  val constraintValue: ∀[[x] => Pow[x] isPowerOf x] = powerFunctionExistence.instance
  def constraint[x : SetDomain, z : SetDomain]: (z ∈ Pow[x]) <=> (z ⊂ x) = {
    forType[z].instantiate[[z] => (z ∈ Pow[x]) <=> (z ⊂ x)](
      forType[x].instantiate[[x] => Pow[x] isPowerOf x](constraintValue)
    )
  }

  implicit def powerIsSet[x]: SetDomain[Pow[x]] = ???

}
