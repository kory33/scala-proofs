package com.github.kory33.proof.set.zf.constructs

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

}
