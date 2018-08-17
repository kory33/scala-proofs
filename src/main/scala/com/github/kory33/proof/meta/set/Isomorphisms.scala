package com.github.kory33.proof.meta.set

import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.set.logic.Equality._
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set.Σ

object Isomorphisms {

  def uniqueness[R[_ <: Σ], X <: Σ](uniqueness: ∃![R], rel: R[X]): X =::= ∃[R]#S = new (X =::= ∃[R]#S) {
    /**
     * Since the subtype of ∃[R]#S is unique to X, they are isomorphic.
     * This means that the cast from F[X] to F[∃[R]#S] is safe for any F[_ <: Σ].
     */
    def sub[F[_ <: Σ]]: F[X] => F[∃[R]#S] = { fx: F[X] => fx.asInstanceOf[F[∃[R]#S]] }
  }

}