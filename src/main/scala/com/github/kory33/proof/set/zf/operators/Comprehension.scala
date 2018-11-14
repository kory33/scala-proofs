package com.github.kory33.proof.set.zf.operators

import scala.language.implicitConversions

import com.github.kory33.proof.meta.set.Isomorphisms

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.logic.propositional.ClassicalLogicSystem._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateSystem._
import com.github.kory33.proof.set.logic.SetDomain
import com.github.kory33.proof.logic.predicate.Equality._
import com.github.kory33.proof.set.axiom.zf._
import com.github.kory33.proof.set.zf.Lemma._
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set._

class ComprehensionConstruct(implicit axiom: ZFExtensionality & ZFSeparation) {

  type isSeparationBy[x, X, F[_]] = ∀[[z] => (z ∈ x) <=> ((z ∈ X) ∧ F[z])]

  type Comprehension[X, F[_]] = ∃[[y] => isSeparationBy[y, X, F]]#S

  def constraint[X : SetDomain, F[_]]: ∀[[x] => (x ∈ Comprehension[X, F]) <=> ((x ∈ X) ∧ F[x])] ∧ SetDomain[Comprehension[X, F]] = {
    type SF[y] = isSeparationBy[y, X, F]

    implicit val existence: ∃[SF] = separate[X, F]
    val uniqueness: Unique[SF] = byContradiction { assumption: ￢[∀[[x] => ∀[[y] => (SF[x] ∧ SF[y]) => x =::= y]]] =>
      implicit val ev1: ∃[[x] => ∃[[y] => ￢[(SF[x] ∧ SF[y]) => x =::= y]]] = notForall2[[x, y] => (SF[x] ∧ SF[y]) => x =::= y](assumption)
      type X1 = ev1.S
      implicit val ev11 = ev1.instance
      type Y1 = ev11.S
      val ev2: ￢[(SF[X1] ∧ SF[Y1]) => X1 =::= Y1] = ev11.instance
      val ev3: (SF[X1] ∧ SF[Y1]) => X1 =::= Y1 = equivalence[X1, Y1, [z] => (z ∈ X) ∧ F[z]]
      ev3 ∧ ev2
    }
    val uniqueExistence: ∃![SF] = existence ∧ uniqueness
    
    type Y = existence.S
    val ev1: SF[Y] = existence.instance
    val ev2: Y =::= Comprehension[X, F] = Isomorphisms.uniqueness(uniqueExistence, ev1)
    val ev3: SF[Comprehension[X, F]] = ev2.sub[SF](ev1)
    val ev4: SetDomain[Y] = implicitly
    val ev5: SetDomain[Comprehension[X, F]] = ev2.sub[SetDomain](ev4)
    ev3 ∧ ev5
  }

  def constraint1[X : SetDomain, F[_]]: ∀[[x] => (x ∈ Comprehension[X, F]) <=> ((x ∈ X) ∧ F[x])] = constraint._1

  implicit def comprehensionIsSet[X : SetDomain, F[_]]: SetDomain[Comprehension[X, F]] = constraint._2

  def constraint2[X : SetDomain, F[_], x : SetDomain]: (x ∈ Comprehension[X, F]) <=> ((x ∈ X) ∧ F[x]) = {
    forType[x].instantiate[[x] => (x ∈ Comprehension[X, F]) <=> ((x ∈ X) ∧ F[x])](constraint1[X, F])
  }

  def subset[X : SetDomain, F[_]]: Comprehension[X, F] ⊂ X = byContradiction { implicit assumption: ∃[[x] => ￢[(x ∈ Comprehension[X, F]) => (x ∈ X)]] =>
    type Y = assumption.S
    val ev1: ￢[(Y ∈ Comprehension[X, F]) => (Y ∈ X)] = assumption.instance
    val ev2: (Y ∈ Comprehension[X, F]) => (Y ∈ X) = { assumption2 => constraint2[X, F, Y].implies(assumption2)._1 }
    ev2 ∧ ev1
  }

  def hasAll[X : SetDomain, F[_]]: Comprehension[X, F] hasAll F = byContradiction { implicit assumption: ∃[[x] => ￢[(x ∈ Comprehension[X, F]) => F[x]]] =>
    type Y = assumption.S
    val ev1: ￢[(Y ∈ Comprehension[X, F]) => F[Y]] = assumption.instance
    val ev2: (Y ∈ Comprehension[X, F]) => F[Y] = { assumption2 => constraint2[X, F, Y].implies(assumption2)._2 }
    ev2 ∧ ev1
  }

}
