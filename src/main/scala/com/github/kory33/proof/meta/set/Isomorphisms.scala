package com.github.kory33.proof.meta.set

import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set.Σ

object Isomorphisms {

  def uniqueness[G[_], R[_ <: Σ], X <: Σ](uniqueness: ∃![R], rel: R[X]): G[X] <=> G[∃[R]#S] = ???

}