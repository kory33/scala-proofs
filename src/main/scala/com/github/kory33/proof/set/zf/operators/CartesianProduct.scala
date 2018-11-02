package com.github.kory33.proof.set.zf.operators

import scala.language.implicitConversions

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateSystem._
import com.github.kory33.proof.set.logic.SetDomain
import com.github.kory33.proof.logic.predicate.Equality._
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

  type ×[X, Y] = Comprehension[Pow[Pow[X ∪ Y]], [z] => X hasSome ([x] => Y hasSome ([y] => z =::= (x ::: y)))]

  def constraint[xy : SetDomain, X : SetDomain, Y : SetDomain]: (xy ∈ (X × Y)) <=> (X hasSome ([x] => Y hasSome ([y] => xy =::= (x ::: y)))) = {
    import pairSet.pairIsSet
    import binaryUnion.binaryUnionIsSet
    import power.powerIsSet

    val ev1: (xy ∈ (X × Y)) <=> ((xy ∈ Pow[Pow[X ∪ Y]]) ∧ (X hasSome ([x] => Y hasSome ([y] => xy =::= (x ::: y))))) = {
      comprehension.constraint2[Pow[Pow[X ∪ Y]], [z] => X hasSome ([x] => Y hasSome ([y] => z =::= (x ::: y))), xy]
    }
    val ev2: (X hasSome ([x] => Y hasSome ([y] => xy =::= (x ::: y)))) => (xy ∈ Pow[Pow[X ∪ Y]]) = { implicit assumption2 =>
      type X1 = assumption2.S
      val ev21: X1 ∈ X = assumption2.instance._1
      implicit val ev22: Y hasSome ([y] => xy =::= (X1 ::: y)) = assumption2.instance._2
      type Y1 = ev22.S
      val ev23: Y1 ∈ Y = ev22.instance._1
      val ev24: xy =::= (X1 ::: Y1) = ev22.instance._2
      val ev25: (X1 ::: Y1) ∈ Pow[Pow[X ∪ Y]] = {
        val ev251: ∀[[z] => (z ∈ (X1 ::: Y1)) => (z ∈ Pow[X ∪ Y])] = byContradiction { implicit assumption251: ∃[[z] => ￢[(z ∈ (X1 ::: Y1)) => (z ∈ Pow[X ∪ Y])]] =>
          type Z = assumption251.S
          val ev2511: ￢[(Z ∈ (X1 ::: Y1)) => (Z ∈ Pow[X ∪ Y])] = assumption251.instance
          val ev2512: (Z ∈ (X1 ::: Y1)) => (Z ∈ Pow[X ∪ Y]) = { zInX1Y1 =>
            val ev25121: (Z =::= Just[X1]) ∨ (Z =::= (X1 ++: Y1)) = pairSet.constraint2[Z, Just[X1], X1 ++: Y1].implies(zInX1Y1)
            val ev25122: (Z =::= Just[X1]) => (Z ∈ Pow[X ∪ Y]) = { assumption25122 =>
              val ev251221: Just[X1] ⊂ (X ∪ Y) = byContradiction { implicit assumption251221: ∃[[w] => ￢[(w ∈ Just[X1]) => (w ∈ (X ∪ Y))]] =>
                type W = assumption251221.S
                val ev2512211: ￢[(W ∈ Just[X1]) => (W ∈ (X ∪ Y))] = assumption251221.instance
                val ev2512212: (W ∈ Just[X1]) => (W ∈ (X ∪ Y)) = { wInJustX1 =>
                  val ev25122121: W =::= X1 = singleton.equalIfContained[W, X1](wInJustX1)
                  val ev25122122: X1 ∈ (X ∪ Y) = binaryUnion.containsLeft[X1, X, Y](ev21)
                  ev25122121.commute.sub[[w] => w ∈ (X ∪ Y)](ev25122122)
                }
                ev2512212 ∧ ev2512211
              }
              power.constraint[X ∪ Y, Z].impliedBy(assumption25122.commute.sub[[z] => z ⊂ (X ∪ Y)](ev251221))
            }
            val ev25123: (Z =::= (X1 ++: Y1)) => (Z ∈ Pow[X ∪ Y]) = { zEqX1Y1 =>
              val ev251231: (X1 ++: Y1) ⊂ (X ∪ Y) = byContradiction { implicit assumption251231: ∃[[w] => ￢[(w ∈ (X1 ++: Y1)) => (w ∈ (X ∪ Y))]] =>
                type W = assumption251231.S
                val ev2512311: ￢[(W ∈ (X1 ++: Y1)) => (W ∈ (X ∪ Y))] = assumption251231.instance
                val ev2512312: (W ∈ (X1 ++: Y1)) => (W ∈ (X ∪ Y)) = { wInX1Y1 =>
                  val ev25123121: (W =::= X1) ∨ (W =::= Y1) = pairSet.constraint2[W, X1, Y1].implies(wInX1Y1)
                  val ev25123122: (W =::= X1) => (W ∈ (X ∪ Y)) = { wEqX1 => binaryUnion.containsLeft(wEqX1.commute.sub[[w] => w ∈ X](ev21)) }
                  val ev25123123: (W =::= Y1) => (W ∈ (X ∪ Y)) = { wEqY1 => binaryUnion.containsRight(wEqY1.commute.sub[[w] => w ∈ Y](ev23)) }
                  removeDisj(ev25123121)(ev25123122)(ev25123123)
                }
                ev2512312 ∧ ev2512311
              }
              power.constraint[X ∪ Y, Z].impliedBy(zEqX1Y1.commute.sub[[z] => z ⊂ (X ∪ Y)](ev251231))
            }
            removeDisj(ev25121)(ev25122)(ev25123)
          }
          ev2512 ∧ ev2511
        }
        val ev252: (X1 ::: Y1) ⊂ Pow[X ∪ Y] = ev251
        power.constraint[Pow[X ∪ Y], (X1 ::: Y1)].impliedBy(ev252)
      }
      ev24.commute.sub[[xy] => xy ∈ Pow[Pow[X ∪ Y]]](ev25)
    }
    val ev3: (xy ∈ (X × Y)) => (X hasSome ([x] => Y hasSome ([y] => xy =::= (x ::: y)))) = ev1.implies.andThen(_._2)
    val ev4: (X hasSome ([x] => Y hasSome ([y] => xy =::= (x ::: y)))) => (xy ∈ (X × Y)) = { assumption4 =>
      ev1.impliedBy(ev2(assumption4) ∧ assumption4)
    }
    ev3 ∧ ev4
  }

  def leftProjection[x : SetDomain, y : SetDomain, X : SetDomain, Y : SetDomain](contained: (x ::: y) ∈ (X × Y)): (x ∈ X) = {
    import orderedPair.setDomain

    implicit val ev1: X hasSome ([x1] => Y hasSome ([y1] => (x ::: y) =::= (x1 ::: y1))) = constraint[(x ::: y), X, Y].implies(contained)
    type X1 = ev1.S;
    val ev2: X1 ∈ X = ev1.instance._1
    implicit val ev3: (Y hasSome ([y1] => (x ::: y) =::= (X1 ::: y1))) = ev1.instance._2
    type Y1 = ev3.S
    val ev4: ((x ::: y) =::= (X1 ::: Y1)) = ev3.instance._2
    val ev5: x =::= X1 = orderedPair.constraint[x, y, X1, Y1].implies(ev4)._1
    ev5.commute.sub[[x1] => x1 ∈ X](ev2)
  }

  def rightProjection[x : SetDomain, y : SetDomain, X : SetDomain, Y : SetDomain](contained: (x ::: y) ∈ (X × Y)): (y ∈ Y) = {
    import orderedPair.setDomain

    implicit val ev1: X hasSome ([x1] => Y hasSome ([y1] => (x ::: y) =::= (x1 ::: y1))) = constraint[(x ::: y), X, Y].implies(contained)
    type X1 = ev1.S
    implicit val ev2: (Y hasSome ([y1] => (x ::: y) =::= (X1 ::: y1))) = ev1.instance._2
    type Y1 = ev2.S
    val ev3: Y1 ∈ Y = ev2.instance._1
    val ev4: ((x ::: y) =::= (X1 ::: Y1)) = ev2.instance._2
    val ev5: y =::= Y1 = orderedPair.constraint[x, y, X1, Y1].implies(ev4)._2
    ev5.commute.sub[[y1] => y1 ∈ Y](ev3)
  }

  def flipProduct[x : SetDomain, y : SetDomain, X : SetDomain, Y : SetDomain](contained: (x ::: y) ∈ (X × Y)): ((y ::: x) ∈ (Y × X)) = {
    // ??
    implicit val yxIsSet: SetDomain[y ::: x] = orderedPair.setDomain[y, x]

    val ev1: x ∈ X = leftProjection[x, y, X, Y](contained)
    val ev2: y ∈ Y = rightProjection[x, y, X, Y](contained)
    type yx = (y ::: x)
    val ev3: yx =::= yx = implicitly
    val ev4: X hasSome ([x1] => yx =::= (y ::: x1)) = forType[x].generalize(ev1 ∧ ev3)
    val ev5: Y hasSome ([y1] => X hasSome ([x1] => yx =::= (y1 ::: x1))) = forType[y].generalize(ev2 ∧ ev4)
    constraint[yx, Y, X].impliedBy(ev5)
  }

}
