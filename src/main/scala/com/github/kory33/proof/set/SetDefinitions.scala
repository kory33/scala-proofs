package com.github.kory33.proof.set

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.predicate.PredicateLogicDefinitions._

object SetDefinitions {

  type ∈[x, y]
  type =#=[x, y]

  type ∉[x, y] = ￢[x ∈ y]
  type =/=[x, y] = ￢[x =#= y]
  type ⊂[x, y] = ∀[[z] => z ∈ x => z ∈ y]
  type ⊃[x, y] = y ⊂ x

  type isEmpty[x] = ∀[[y] => y ∉ x]

}
