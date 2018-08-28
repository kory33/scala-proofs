package com.github.kory33.proof.set.zf.operators

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.set.logic.SpecializedPredicateSystem._
import com.github.kory33.proof.set.logic.Equality._
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set._

class CartesianProductConstruct(val comprehension: ComprehensionConstruct,
                                val power: PowerSetConstruct,
                                val binaryUnion: BinaryUnionConstruct,
                                val orderedPair: OrderedPairConstruct) {

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
      val ev25: (X1 ::: Y1) ∈ Pow[Pow[X ∪ Y]] = ???
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
