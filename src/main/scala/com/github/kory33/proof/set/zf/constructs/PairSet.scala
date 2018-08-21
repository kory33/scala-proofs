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
    byContradiction { assumption: ∃[[x <: Σ] => ￢[∀[[y <: Σ] => ∃[[z <: Σ] => containsTwo[z, x, y]]]]] =>
      type X = assumption.S
      val ev1: ∃[[y <: Σ] => ￢[∃[[z <: Σ] => containsTwo[z, X, y]]]] = assumption.value
      type Y = ev1.S
      val ev2: ￢[∃[[z <: Σ] => containsTwo[z, X, Y]]] = ev1.value
      val ev3: ∃[[z <: Σ] => ∀[[w <: Σ] => ((w =::= X) ∨ (w =::= Y)) => (w ∈ z)]] = {
        forType2[X, Y].instantiate[[a <: Σ, b <: Σ] => ∃[[x <: Σ] => ∀[[w <: Σ] => ((w =::= a) ∨ (w =::= b)) => (w ∈ x)]]](axiom.pairing)
      }
      val ev4: ∃[[z <: Σ] => containsTwo[z, X, Y]] = comprehendsExactly[[w <: Σ] => ((w =::= X) ∨ (w =::= Y))](ev3)
      ev4 ∧ ev2
    }
  }

  val uniqueness: ∀[[x <: Σ] => ∀[[y <: Σ] => Unique[[z <: Σ] => containsTwo[z, x, y]]]] = {
    byContradiction { assumption: ∃[[x <: Σ] => ￢[∀[[y <: Σ] => Unique[[z <: Σ] => containsTwo[z, x, y]]]]] =>
      type X = assumption.S
      val ev1: ∃[[y <: Σ] => ￢[Unique[[z <: Σ] => containsTwo[z, X, y]]]] = assumption.value
      type Y = ev1.S
      val ev2: ∃[[z <: Σ] => ￢[∀[[w <: Σ] => (containsTwo[z, X, Y] ∧ containsTwo[w, X, Y]) => z =::= w]]] = ev1.value
      type Z = ev2.S
      val ev3: ∃[[w <: Σ] => ￢[(containsTwo[Z, X, Y] ∧ containsTwo[w, X, Y]) => Z =::= w]] = ev2.value
      type W = ev3.S
      val ev4: ￢[(containsTwo[Z, X, Y] ∧ containsTwo[W, X, Y]) => Z =::= W] = ev3.value
      val ev5: (containsTwo[Z, X, Y] ∧ containsTwo[W, X, Y]) => Z =::= W = equivalence[Z, W, [z <: Σ] => (z =::= X) ∨ (z =::= Y)]
      ev5 ∧ ev4
    }
  }

  val pairFunctionExistence: ∃~~>[[++:[_ <: Σ, _ <: Σ] <: Σ] => ∀[[x <: Σ] => ∀[[y <: Σ] => containsTwo[x ++: y, x, y]]]] = {
    createBinaryClassFunction[containsTwo](uniqueExistence2[containsTwo](existence, uniqueness))
  }

  type ++:[x <: Σ, y <: Σ] = pairFunctionExistence.F[x, y]
  val constraint: ∀[[x <: Σ] => ∀[[y <: Σ] => containsTwo[x ++: y, x, y]]] = pairFunctionExistence.value

}

class SingletonConstruct(val pairSet: PairSetConstruct) {

  type ++: = pairSet.++:

  type Just[x <: Σ] = x ++: x
  val constraint: ∀[[x <: Σ] => Just[x] isSingletonOf x] = byContradiction { assumption: ∃[[x <: Σ] => ￢[Just[x] isSingletonOf x]] =>
    type X = assumption.S
    val ev1: ￢[Just[X] isSingletonOf X] = assumption.value
    val ev2: containsTwo[Just[X], X, X] = forType[X].instantiate[[y <: Σ] => containsTwo[X ++: y, X, y]](
      forType[X].instantiate[[x <: Σ] => ∀[[y <: Σ] => containsTwo[x ++: y, x, y]]](pairSet.constraint)
    )
    val ev3: ∀[[w <: Σ] => (w ∈ Just[X]) <=> ((w =::= X) ∨ (w =::= X))] = ev2
    val ev4: ∀[[w <: Σ] => (w ∈ Just[X]) <=> (w =::= X)] = byContradiction { assumption4: ∃[[w <: Σ] => ￢[(w ∈ Just[X]) <=> (w =::= X)]] =>
      type W = assumption4.S
      val ev41: ￢[(W ∈ Just[X]) <=> (W =::= X)] = assumption4.value
      val ev42: (W ∈ Just[X]) <=> ((W =::= X) ∨ (W =::= X)) = forType[W].instantiate[[w <: Σ] => (w ∈ Just[X]) <=> ((w =::= X) ∨ (w =::= X))](ev3)
      val ev43: ((W =::= X) ∨ (W =::= X)) <=> (W =::= X) = {
        val implies = { from: (W =::= X) ∨ (W =::= X) => removeDisj(from)(identity)(identity) }
        val impliedBy: ((W =::= X) ∨ (W =::= X)) <= (W =::= X) = Left.apply
        implies ∧ impliedBy
      }
      val ev44: (W ∈ Just[X]) <=> (W =::= X) = ev42.andThen(ev43)
      ev44 ∧ ev41
    }
    ev4 ∧ ev1
  }

}
