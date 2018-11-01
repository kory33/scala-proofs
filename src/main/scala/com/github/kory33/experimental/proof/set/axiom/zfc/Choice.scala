package com.github.kory33.experimental.proof.set.axiom.zfc

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.experimental.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.experimental.proof.logic.predicate.Equality._
import com.github.kory33.experimental.proof.set._
import com.github.kory33.experimental.proof.set.SetDefinitions._

/**
  * For every family F of disjoint nonempty sets there exists a selector S that intersects every x ∈ F in precisely one point.
  */
trait Choice {
  def choice: ∀[[F] => ((F hasAll ([x] => ￢[isEmpty[x]])) ∧ isPairwiseDisjoint[F]) => ∃[[S] => S isASelectorOn F]]
}