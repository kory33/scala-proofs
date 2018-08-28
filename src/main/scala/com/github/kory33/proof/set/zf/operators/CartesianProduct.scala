package com.github.kory33.proof.set.zf.operators

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
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
    ???
  }
  def flipProduct[x <: Σ, y <: Σ, X <: Σ, Y <: Σ]: ((x ::: y) ∈ (X × Y)) => ((y ::: x) ∈ (Y × X)) = {
    ???
  }

  def leftProjection[x <: Σ, y <: Σ, X <: Σ, Y <: Σ](leftContained: (x ::: y) ∈ (X × Y)): (x ∈ X) = {
    val ev1: X hasSome ([x1 <: Σ] => Y hasSome ([y1 <: Σ] => (x ::: y) =::= (x1 ::: y1))) = constraint[(x ::: y), X, Y].implies(leftContained)
    type X1 = ev1.S;
    val ev2: X1 ∈ X = ev1.value._1
    val ev3: (Y hasSome ([y1 <: Σ] => (x ::: y) =::= (X1 ::: y1))) = ev1.value._2
    type Y1 = ev3.S
    val ev4: ((x ::: y) =::= (X1 ::: Y1)) = ev3.value._2
    val ev5: x =::= X1 = orderedPair.constraint[x, y, X1, Y1].implies(ev4)._1
    ev5.commute.sub[[x1 <: Σ] => x1 ∈ X](ev2)
  }

  def rightProjection[x <: Σ, y <: Σ, X <: Σ, Y <: Σ](rightContained: (x ::: y) ∈ (X × Y)): (y ∈ Y) = leftProjection(flipProduct(rightContained))

}
