package com.github.kory33.proof.set.zf.operators

import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set._

class DifferenceConstruct(val comprehension: ComprehensionConstruct) {

  type \[x <: Σ, y <: Σ] = comprehension.Comprehension[x, [z <: Σ] => z ∉ y]

}

class SymmetricDifferenceConstruct(val difference: DifferenceConstruct, val binaryUnion: BinaryUnionConstruct) {

  type \ = difference.\
  type ∪ = binaryUnion.∪
  type Δ[x <: Σ, y <: Σ] = (x \ y) ∪ (y \ x)

}
