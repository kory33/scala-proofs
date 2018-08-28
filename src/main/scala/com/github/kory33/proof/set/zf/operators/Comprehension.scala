package com.github.kory33.proof.set.zf.operators

import scala.language.implicitConversions

import com.github.kory33.proof.meta.set.Isomorphisms

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.logic.propositional.ClassicalLogicSystem._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateSystem._
import com.github.kory33.proof.set.logic.Equality._
import com.github.kory33.proof.set.axiom.zf._
import com.github.kory33.proof.set.zf.Lemma._
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set._

class ComprehensionConstruct(implicit axiom: ZFExtensionality & ZFSeparation) {

  type isSeparationBy[x <: Σ, X <: Σ, F[_ <: Σ]] = ∀[[z <: Σ] => (z ∈ x) <=> ((z ∈ X) ∧ F[z])]

  type Comprehension[X <: Σ, F[_ <: Σ]] = ∃[[y <: Σ] => isSeparationBy[y, X, F]]#S

  def constraint[X <: Σ, F[_ <: Σ]]: ∀[[x <: Σ] => (x ∈ Comprehension[X, F]) <=> ((x ∈ X) ∧ F[x])] = {
    type SF[y <: Σ] = isSeparationBy[y, X, F]

    val existence: ∃[SF] = separate[X, F]
    val uniqueness: Unique[SF] = byContradiction { assumption: ￢[∀[[x <: Σ] => ∀[[y <: Σ] => (SF[x] ∧ SF[y]) => x =::= y]]] =>
      val ev1: ∃[[x <: Σ] => ∃[[y <: Σ] => ￢[(SF[x] ∧ SF[y]) => x =::= y]]] = notForall2[[x <: Σ, y <: Σ] => (SF[x] ∧ SF[y]) => x =::= y](assumption)
      type X1 = ev1.S; type Y1 = ev1.value.S
      val ev2: ￢[(SF[X1] ∧ SF[Y1]) => X1 =::= Y1] = ev1.value.value
      val ev3: (SF[X1] ∧ SF[Y1]) => X1 =::= Y1 = equivalence[X1, Y1, [z <: Σ] => (z ∈ X) ∧ F[z]]
      ev3 ∧ ev2
    }
    val uniqueExistence: ∃![SF] = existence ∧ uniqueness
    
    type Y = existence.S
    val ev1: SF[Y] = existence.value
    val ev2: SF[Comprehension[X, F]] = Isomorphisms.uniqueness(uniqueExistence, ev1).sub[SF](ev1)
    ev2
  }

  def constraint2[X <: Σ, F[_ <: Σ], x <: Σ]: (x ∈ Comprehension[X, F]) <=> ((x ∈ X) ∧ F[x]) = {
    forType[x].instantiate[[x <: Σ] => (x ∈ Comprehension[X, F]) <=> ((x ∈ X) ∧ F[x])](constraint[X, F])
  }

}
