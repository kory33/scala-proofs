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

class PairSetConstruct(implicit axiom: ZFExtensionality & ZFSeparation & ZFParing) {

  val existence: ∀[[x <: Σ] => ∀[[y <: Σ] => ∃[[z <: Σ] => containsTwo[z, x, y]]]] = {
    byContradiction { assumption: ￢[∀[[x <: Σ] => ∀[[y <: Σ] => ∃[[z <: Σ] => containsTwo[z, x, y]]]]] =>
      val ev1: ∃[[x <: Σ] => ∃[[y <: Σ] => ￢[∃[[z <: Σ] => containsTwo[z, x, y]]]]] = notForall2[[x <: Σ, y <: Σ] => ∃[[z <: Σ] => containsTwo[z, x, y]]](assumption)
      type X = ev1.S; type Y = ev1.value.S
      val ev2: ￢[∃[[z <: Σ] => containsTwo[z, X, Y]]] = ev1.value.value
      val ev3: ∃[[z <: Σ] => ∀[[w <: Σ] => ((w =::= X) ∨ (w =::= Y)) => (w ∈ z)]] = {
        forType2[X, Y].instantiate[[a <: Σ, b <: Σ] => ∃[[x <: Σ] => ∀[[w <: Σ] => ((w =::= a) ∨ (w =::= b)) => (w ∈ x)]]](axiom.pairing)
      }
      val ev4: ∃[[z <: Σ] => containsTwo[z, X, Y]] = comprehendsExactly[[w <: Σ] => ((w =::= X) ∨ (w =::= Y))](ev3)
      ev4 ∧ ev2
    }
  }

  val uniqueness: ∀[[x <: Σ] => ∀[[y <: Σ] => Unique[[z <: Σ] => containsTwo[z, x, y]]]] = {
    byContradiction { assumption: ￢[∀[[x <: Σ] => ∀[[y <: Σ] => Unique[[z <: Σ] => containsTwo[z, x, y]]]]] =>
      val ev1: ∃[[x <: Σ] => ∃[[y <: Σ] => ∃[[z <: Σ] => ∃[[w <: Σ] => ￢[(containsTwo[z, x, y] ∧ containsTwo[w, x, y]) => z =::= w]]]]] = {
        notForall4[[x <: Σ, y <: Σ, z <: Σ, w <: Σ] => (containsTwo[z, x, y] ∧ containsTwo[w, x, y]) => z =::= w](assumption)
      }
      type X = ev1.S; type Y = ev1.value.S; type Z = ev1.value.value.S; type W = ev1.value.value.value.S
      val ev2: ￢[(containsTwo[Z, X, Y] ∧ containsTwo[W, X, Y]) => Z =::= W] = ev1.value.value.value.value
      val ev3: (containsTwo[Z, X, Y] ∧ containsTwo[W, X, Y]) => Z =::= W = equivalence[Z, W, [z <: Σ] => (z =::= X) ∨ (z =::= Y)]
      ev3 ∧ ev2
    }
  }

  val pairFunctionExistence: ∃~~>[[++:[_ <: Σ, _ <: Σ] <: Σ] => ∀[[x <: Σ] => ∀[[y <: Σ] => containsTwo[x ++: y, x, y]]]] = {
    createBinaryClassFunction[containsTwo](uniqueExistence2[containsTwo](existence, uniqueness))
  }

  type ++:[x <: Σ, y <: Σ] = pairFunctionExistence.F[x, y]
  val constraintValue: ∀[[x <: Σ] => ∀[[y <: Σ] => containsTwo[x ++: y, x, y]]] = pairFunctionExistence.value
  def constraint[x <: Σ, y <: Σ]: containsTwo[x ++: y, x, y] = {
    forType2[x, y].instantiate[[x <: Σ, y <: Σ] => containsTwo[x ++: y, x, y]](constraintValue)
  }

  def containsLeft[x <: Σ, y <: Σ]: x ∈ (x ++: y) = {
    forType[x].instantiate[[w <: Σ] => (w ∈ (x ++: y) <=> ((w =::= x) ∨ (w =::= y)))](constraint).impliedBy(Left(implicitly[x =::= x]))
  }

  def containsRight[x <: Σ, y <: Σ]: y ∈ (x ++: y) = {
    forType[y].instantiate[[w <: Σ] => (w ∈ (x ++: y) <=> ((w =::= x) ∨ (w =::= y)))](constraint).impliedBy(Right(implicitly[y =::= y]))
  }

}

class SingletonConstruct(val pairSet: PairSetConstruct) {

  type ++: = pairSet.++:

  type Just[x <: Σ] = x ++: x
  val constraintValue: ∀[[x <: Σ] => Just[x] isSingletonOf x] = byContradiction { assumption: ∃[[x <: Σ] => ￢[Just[x] isSingletonOf x]] =>
    type X = assumption.S
    val ev1: ￢[Just[X] isSingletonOf X] = assumption.value
    val ev2: ∀[[w <: Σ] => (w ∈ Just[X]) <=> (w =::= X)] = byContradiction { assumption4: ∃[[w <: Σ] => ￢[(w ∈ Just[X]) <=> (w =::= X)]] =>
      type W = assumption4.S
      val ev21: ￢[(W ∈ Just[X]) <=> (W =::= X)] = assumption4.value
      val ev22: containsTwo[Just[X], X, X] = pairSet.constraint[X, X]
      val ev23: (W ∈ Just[X]) <=> ((W =::= X) ∨ (W =::= X)) = forType[W].instantiate[[w <: Σ] => (w ∈ Just[X]) <=> ((w =::= X) ∨ (w =::= X))](ev22)
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
  def constraint[x <: Σ]: Just[x] isSingletonOf x = forType[x].instantiate[[x <: Σ] => Just[x] isSingletonOf x](constraintValue)

  def contains[x <: Σ]: x ∈ Just[x] = pairSet.containsLeft

  def equalIfContained[x <: Σ, y <: Σ]: (x ∈ Just[y]) => (x =::= y) = { assumption =>
    forType[x].instantiate[[z <: Σ] => (z ∈ Just[y]) <=> (z =::= y)](constraint[y]).implies(assumption)
  }

  def equality[x <: Σ, y <: Σ]: (Just[x] =::= Just[y]) => (x =::= y) = { assumption =>
    val ev1: Just[y] isSingletonOf x = assumption.sub[[justY <: Σ] => justY isSingletonOf x](constraint[x])
    val ev2: (y ∈ Just[y]) <=> (y =::= x) = forType[y].instantiate[[z <: Σ] => (z ∈ Just[y]) <=> (z =::= x)](ev1)
    ev2.implies(contains).commute
  }

}
