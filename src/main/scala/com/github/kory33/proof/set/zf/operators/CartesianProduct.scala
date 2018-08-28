package com.github.kory33.proof.set.zf.operators

import scala.language.implicitConversions

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateSystem._
import com.github.kory33.proof.set.logic.Equality._
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set._

class CartesianProductConstruct(val comprehension: ComprehensionConstruct,
                                val power: PowerSetConstruct,
                                val binaryUnion: BinaryUnionConstruct,
                                val orderedPair: OrderedPairConstruct) {

  val singleton: orderedPair.singleton.type = orderedPair.singleton
  val pairSet: orderedPair.singleton.pairSet.type = singleton.pairSet

  type Just = singleton.Just
  type ++: = pairSet.++:
  
  type Comprehension = comprehension.Comprehension
  type Pow = power.Pow
  type ::: = orderedPair.:::
  type ∪ = binaryUnion.∪

  type ×[X <: Σ, Y <: Σ] = Comprehension[Pow[Pow[X ∪ Y]], [z <: Σ] => X hasSome ([x <: Σ] => Y hasSome ([y <: Σ] => z =::= (x ::: y)))]

  def constraint[xy <: Σ, X <: Σ, Y <: Σ]: (xy ∈ (X × Y)) <=> (X hasSome ([x <: Σ] => Y hasSome ([y <: Σ] => xy =::= (x ::: y)))) = {
    val ev1: (xy ∈ (X × Y)) <=> ((xy ∈ Pow[Pow[X ∪ Y]]) ∧ (X hasSome ([x <: Σ] => Y hasSome ([y <: Σ] => xy =::= (x ::: y))))) = {
      comprehension.constraint2[Pow[Pow[X ∪ Y]], [z <: Σ] => X hasSome ([x <: Σ] => Y hasSome ([y <: Σ] => z =::= (x ::: y))), xy]
    }
    val ev2: (X hasSome ([x <: Σ] => Y hasSome ([y <: Σ] => xy =::= (x ::: y)))) => (xy ∈ Pow[Pow[X ∪ Y]]) = { assumption2 =>
      type X1 = assumption2.S
      val ev21: X1 ∈ X = assumption2.value._1
      val ev22: Y hasSome ([y <: Σ] => xy =::= (X1 ::: y)) = assumption2.value._2
      type Y1 = ev22.S
      val ev23: Y1 ∈ Y = ev22.value._1
      val ev24: xy =::= (X1 ::: Y1) = ev22.value._2
      val ev25: (X1 ::: Y1) ∈ Pow[Pow[X ∪ Y]] = {
        val ev251: ∀[[z <: Σ] => (z ∈ (X1 ::: Y1)) => (z ∈ Pow[X ∪ Y])] = byContradiction { assumption251: ∃[[z <: Σ] => ￢[(z ∈ (X1 ::: Y1)) => (z ∈ Pow[X ∪ Y])]] =>
          type Z = assumption251.S
          val ev2511: ￢[(Z ∈ (X1 ::: Y1)) => (Z ∈ Pow[X ∪ Y])] = assumption251.value
          val ev2512: (Z ∈ (X1 ::: Y1)) => (Z ∈ Pow[X ∪ Y]) = { zInX1Y1 =>
            val ev25121: (Z =::= Just[X1]) ∨ (Z =::= (X1 ++: Y1)) = pairSet.constraint2[Z, Just[X1], X1 ++: Y1].implies(zInX1Y1)
            val ev25122: (Z =::= Just[X1]) => (Z ∈ Pow[X ∪ Y]) = { assumption25122 =>
              val ev251221: Just[X1] ⊂ (X ∪ Y) = byContradiction { assumption251221: ∃[[w <: Σ] => ￢[(w ∈ Just[X1]) => (w ∈ (X ∪ Y))]] =>
                type W = assumption251221.S
                val ev2512211: ￢[(W ∈ Just[X1]) => (W ∈ (X ∪ Y))] = assumption251221.value
                val ev2512212: (W ∈ Just[X1]) => (W ∈ (X ∪ Y)) = { wInJustX1 =>
                  val ev25122121: W =::= X1 = singleton.equalIfContained[W, X1](wInJustX1)
                  val ev25122122: X1 ∈ (X ∪ Y) = binaryUnion.containsLeft[X1, X, Y](ev21)
                  ev25122121.commute.sub[[w <: Σ] => w ∈ (X ∪ Y)](ev25122122)
                }
                ev2512212 ∧ ev2512211
              }
              power.constraint[X ∪ Y, Z].impliedBy(assumption25122.commute.sub[[z <: Σ] => z ⊂ (X ∪ Y)](ev251221))
            }
            val ev25123: (Z =::= (X1 ++: Y1)) => (Z ∈ Pow[X ∪ Y]) = { zEqX1Y1 =>
              val ev251231: (X1 ++: Y1) ⊂ (X ∪ Y) = byContradiction { assumption251231: ∃[[w <: Σ] => ￢[(w ∈ (X1 ++: Y1)) => (w ∈ (X ∪ Y))]] =>
                type W = assumption251231.S
                val ev2512311: ￢[(W ∈ (X1 ++: Y1)) => (W ∈ (X ∪ Y))] = assumption251231.value
                val ev2512312: (W ∈ (X1 ++: Y1)) => (W ∈ (X ∪ Y)) = { wInX1Y1 =>
                  val ev25123121: (W =::= X1) ∨ (W =::= Y1) = pairSet.constraint2[W, X1, Y1].implies(wInX1Y1)
                  val ev25123122: (W =::= X1) => (W ∈ (X ∪ Y)) = { wEqX1 => binaryUnion.containsLeft(wEqX1.commute.sub[[w <: Σ] => w ∈ X](ev21)) }
                  val ev25123123: (W =::= Y1) => (W ∈ (X ∪ Y)) = { wEqY1 => binaryUnion.containsRight(wEqY1.commute.sub[[w <: Σ] => w ∈ Y](ev23)) }
                  removeDisj(ev25123121)(ev25123122)(ev25123123)
                }
                ev2512312 ∧ ev2512311
              }
              power.constraint[X ∪ Y, Z].impliedBy(zEqX1Y1.commute.sub[[z <: Σ] => z ⊂ (X ∪ Y)](ev251231))
            }
            removeDisj(ev25121)(ev25122)(ev25123)
          }
          ev2512 ∧ ev2511
        }
        val ev252: (X1 ::: Y1) ⊂ Pow[X ∪ Y] = ev251
        power.constraint[Pow[X ∪ Y], (X1 ::: Y1)].impliedBy(ev252)
      }
      ev24.commute.sub[[xy <: Σ] => xy ∈ Pow[Pow[X ∪ Y]]](ev25)
    }
    val ev3: (xy ∈ (X × Y)) => (X hasSome ([x <: Σ] => Y hasSome ([y <: Σ] => xy =::= (x ::: y)))) = ev1.implies.andThen(_._2)
    val ev4: (X hasSome ([x <: Σ] => Y hasSome ([y <: Σ] => xy =::= (x ::: y)))) => (xy ∈ (X × Y)) = { assumption4 =>
      ev1.impliedBy(ev2(assumption4) ∧ assumption4)
    }
    ev3 ∧ ev4
  }

  def leftProjection[x <: Σ, y <: Σ, X <: Σ, Y <: Σ](contained: (x ::: y) ∈ (X × Y)): (x ∈ X) = {
    val ev1: X hasSome ([x1 <: Σ] => Y hasSome ([y1 <: Σ] => (x ::: y) =::= (x1 ::: y1))) = constraint[(x ::: y), X, Y].implies(contained)
    type X1 = ev1.S;
    val ev2: X1 ∈ X = ev1.value._1
    val ev3: (Y hasSome ([y1 <: Σ] => (x ::: y) =::= (X1 ::: y1))) = ev1.value._2
    type Y1 = ev3.S
    val ev4: ((x ::: y) =::= (X1 ::: Y1)) = ev3.value._2
    val ev5: x =::= X1 = orderedPair.constraint[x, y, X1, Y1].implies(ev4)._1
    ev5.commute.sub[[x1 <: Σ] => x1 ∈ X](ev2)
  }

  def rightProjection[x <: Σ, y <: Σ, X <: Σ, Y <: Σ](contained: (x ::: y) ∈ (X × Y)): (y ∈ Y) = {
    val ev1: X hasSome ([x1 <: Σ] => Y hasSome ([y1 <: Σ] => (x ::: y) =::= (x1 ::: y1))) = constraint[(x ::: y), X, Y].implies(contained)
    type X1 = ev1.S;
    val ev2: (Y hasSome ([y1 <: Σ] => (x ::: y) =::= (X1 ::: y1))) = ev1.value._2
    type Y1 = ev2.S
    val ev3: Y1 ∈ Y = ev2.value._1
    val ev4: ((x ::: y) =::= (X1 ::: Y1)) = ev2.value._2
    val ev5: y =::= Y1 = orderedPair.constraint[x, y, X1, Y1].implies(ev4)._2
    ev5.commute.sub[[y1 <: Σ] => y1 ∈ Y](ev3)
  }

  def flipProduct[x <: Σ, y <: Σ, X <: Σ, Y <: Σ](contained: (x ::: y) ∈ (X × Y)): ((y ::: x) ∈ (Y × X)) = {
    val ev1: x ∈ X = leftProjection(contained)
    val ev2: y ∈ Y = rightProjection(contained)
    type yx = (y ::: x)
    val ev3: yx =::= yx = implicitly
    val ev4: X hasSome ([x1 <: Σ] => yx =::= (y ::: x1)) = forType[x].generalize(ev1 ∧ ev3)
    val ev5: Y hasSome ([y1 <: Σ] => X hasSome ([x1 <: Σ] => yx =::= (y1 ::: x1))) = forType[y].generalize(ev2 ∧ ev4)
    constraint[yx, Y, X].impliedBy(ev5)
  }

}
