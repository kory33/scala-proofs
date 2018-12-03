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

class PairSetConstruct(implicit axiom: ZFExtensionality & ZFSeparation & ZFParing) {

  val existence: ∀[[x] => ∀[[y] => ∃[[z] => containsTwo[z, x, y]]]] = {
    byContradiction { assumption: ￢[∀[[x] => ∀[[y] => ∃[[z] => containsTwo[z, x, y]]]]] =>
      implicit val ev1: ∃[[x] => ∃[[y] => ￢[∃[[z] => containsTwo[z, x, y]]]]] = notForall2[[x, y] => ∃[[z] => containsTwo[z, x, y]]](assumption)
      type X = ev1.S
      implicit val ev11 = ev1.instance
      type Y = ev11.S
      val ev2: ￢[∃[[z] => containsTwo[z, X, Y]]] = ev11.instance
      val ev3: ∃[[z] => ∀[[w] => ((w =::= X) ∨ (w =::= Y)) => (w ∈ z)]] = {
        forType2[X, Y].instantiate[[a, b] => ∃[[x] => ∀[[w] => ((w =::= a) ∨ (w =::= b)) => (w ∈ x)]]](axiom.pairing)
      }
      val ev4: ∃[[z] => containsTwo[z, X, Y]] = comprehendsExactly[[w] => ((w =::= X) ∨ (w =::= Y))](ev3)
      ev4 ∧ ev2
    }
  }

  val uniqueness: ∀[[x] => ∀[[y] => Unique[[z] => containsTwo[z, x, y]]]] = {
    byContradiction { assumption: ￢[∀[[x] => ∀[[y] => Unique[[z] => containsTwo[z, x, y]]]]] =>
      implicit val ev1: ∃[[x] => ∃[[y] => ∃[[z] => ∃[[w] => ￢[(containsTwo[z, x, y] ∧ containsTwo[w, x, y]) => z =::= w]]]]] = {
        notForall4[[x, y, z, w] => (containsTwo[z, x, y] ∧ containsTwo[w, x, y]) => z =::= w](assumption)
      }
      type X = ev1.S
      implicit val ev11 = ev1.instance
      type Y = ev11.S
      implicit val ev12 = ev11.instance
      type Z = ev12.S
      implicit val ev13 = ev12.instance
      type W = ev13.S
      val ev2: ￢[(containsTwo[Z, X, Y] ∧ containsTwo[W, X, Y]) => Z =::= W] = ev13.instance
      val ev3: (containsTwo[Z, X, Y] ∧ containsTwo[W, X, Y]) => Z =::= W = equivalence[Z, W, [z] => (z =::= X) ∨ (z =::= Y)]
      ev3 ∧ ev2
    }
  }

  val pairFunctionExistence: ∃~~>[[++:[_, _]] => ∀[[x] => ∀[[y] => containsTwo[x ++: y, x, y]]]] = {
    createBinaryClassFunction[containsTwo](uniqueExistence2[containsTwo](existence, uniqueness))
  }

  type ++:[x, y] = pairFunctionExistence.F[x, y]
  val constraintValue: ∀[[x] => ∀[[y] => containsTwo[x ++: y, x, y]]] = pairFunctionExistence.instance

  def constraint[x : SetDomain, y : SetDomain]: containsTwo[x ++: y, x, y] = {
    forType2[x, y].instantiate[[x, y] => containsTwo[x ++: y, x, y]](constraintValue)
  }

  def constraint2[z : SetDomain, x : SetDomain, y : SetDomain]: (z ∈ (x ++: y)) <=> ((z =::= x) ∨ (z =::= y)) = {
    forType[z].instantiate[[w] => (w ∈ (x ++: y)) <=> ((w =::= x) ∨ (w =::= y))](constraint)
  }

  def containsLeft[x : SetDomain, y : SetDomain]: x ∈ (x ++: y) = constraint2[x, x, y].impliedBy(Left(implicitly[x =::= x]))

  def containsRight[x : SetDomain, y : SetDomain]: y ∈ (x ++: y) = constraint2[y, x, y].impliedBy(Right(implicitly[y =::= y]))

  implicit def pairIsSet[x: SetDomain, y: SetDomain]: SetDomain[x ++: y] = pairFunctionExistence.typeclass[x, y]

}

class SingletonConstruct(val pairSet: PairSetConstruct) {

  type ++: = pairSet.++:

  type Just[x] = x ++: x
  val constraintValue: ∀[[x] => Just[x] isSingletonOf x] = byContradiction { implicit assumption: ∃[[x] => ￢[Just[x] isSingletonOf x]] =>
    type X = assumption.S
    val ev1: ￢[Just[X] isSingletonOf X] = assumption.instance
    val ev2: ∀[[w] => (w ∈ Just[X]) <=> (w =::= X)] = byContradiction { implicit assumption4: ∃[[w] => ￢[(w ∈ Just[X]) <=> (w =::= X)]] =>
      type W = assumption4.S
      val ev21: ￢[(W ∈ Just[X]) <=> (W =::= X)] = assumption4.instance
      val ev22: containsTwo[Just[X], X, X] = pairSet.constraint[X, X]
      val ev23: (W ∈ Just[X]) <=> ((W =::= X) ∨ (W =::= X)) = forType[W].instantiate[[w] => (w ∈ Just[X]) <=> ((w =::= X) ∨ (w =::= X))](ev22)
      val ev24: ((W =::= X) ∨ (W =::= X)) <=> (W =::= X) = {
        val implies = { from: (W =::= X) ∨ (W =::= X) => removeDisj(from)(identity)(identity) }
        val impliedBy: ((W =::= X) ∨ (W =::= X)) <= (W =::= X) = Left.apply
        implies ∧ impliedBy
      }
      val ev25: (W ∈ Just[X]) <=> (W =::= X) = ev23.andThen(ev24)
      ev25 ∧ ev21
    }
    ev2 ∧ ev1
  }

  def constraint[x : SetDomain]: Just[x] isSingletonOf x = forType[x].instantiate[[x] => Just[x] isSingletonOf x](constraintValue)

  def contains[x : SetDomain]: x ∈ Just[x] = pairSet.containsLeft

  def equalIfContained[x : SetDomain, y : SetDomain](contained: (x ∈ Just[y])): (x =::= y) = {
    forType[x].instantiate[[z] => (z ∈ Just[y]) <=> (z =::= y)](constraint[y]).implies(contained)
  }

  def equality[x : SetDomain, y : SetDomain]: (Just[x] =::= Just[y]) => (x =::= y) = { assumption =>
    val ev1: Just[y] isSingletonOf x = assumption.sub[[justY] => justY isSingletonOf x](constraint[x])
    val ev2: (y ∈ Just[y]) <=> (y =::= x) = forType[y].instantiate[[z] => (z ∈ Just[y]) <=> (z =::= x)](ev1)
    ev2.implies(contains).commute
  }

}
