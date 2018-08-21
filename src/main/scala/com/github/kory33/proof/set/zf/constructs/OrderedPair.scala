package com.github.kory33.proof.set.zf.constructs

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.set.logic.Equality._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateSystem._
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set._

class OrderedPairConstruct(val pairSet: PairSetConstruct, val singleton: SingletonConstruct) {

  type ++:[a <: Σ, b <: Σ] = pairSet.++:[a, b]
  type Just[a <: Σ] = singleton.Just[a]

  type :::[a <: Σ, b <: Σ] = Just[a] ++: Just[a ++: b]
  val constraintValue: ∀[[a <: Σ] => ∀[[b <: Σ] => ∀[[c <: Σ] => ∀[[d <: Σ] => ((a ::: b) =::= (c ::: d)) <=> ((a =::= c) ∧ (b =::= d))]]]] = ???

  def constraint[a <: Σ, b <: Σ, c <: Σ, d <: Σ]: ((a ::: b) =::= (c ::: d)) <=> ((a =::= c) ∧ (b =::= d)) = {
    forType2[c, d].instantiate[[c1 <: Σ, d1 <: Σ] => ((a ::: b) =::= (c1 ::: d1)) <=> ((a =::= c1) ∧ (b =::= d1))](
      forType2[a, b].instantiate[[a1 <: Σ, b1 <: Σ] => ∀[[c1 <: Σ] => ∀[[d1 <: Σ] => ((a1 ::: b1) =::= (c1 ::: d1)) <=> ((a1 =::= c1) ∧ (b1 =::= d1))]]](
        constraintValue
      )
    )
  }

}
