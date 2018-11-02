package com.github.kory33.proof.set.zf.operators

import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set._

class DifferenceConstruct(val comprehension: ComprehensionConstruct) {

  type \[x, y] = comprehension.Comprehension[x, [z] => z ∉ y]

}

class SymmetricDifferenceConstruct(val difference: DifferenceConstruct, val binaryUnion: BinaryUnionConstruct) {

  type \ = difference.\
  type ∪ = binaryUnion.∪
  type Δ[x, y] = (x \ y) ∪ (y \ x)

}
