package com.github.kory33.experimental.proof.meta.set

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.experimental.proof.logic.predicate.Equality._
import com.github.kory33.experimental.proof.set.SetDefinitions._
import com.github.kory33.experimental.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.experimental.proof.set.logic.SetDomain

object Isomorphisms {

  def uniqueness[R[_], X : SetDomain](uniqueness: ∃![R], rel: R[X]): X =::= ∃[R]#S = new (X =::= ∃[R]#S) {
    /**
     * Since the subtype of ∃[R]#S is unique to X, they are isomorphic.
     * This means that the cast from F[X] to F[∃[R]#S] is safe for any F[_].
     */
    def sub[F[_]]: F[X] => F[∃[R]#S] = { fx: F[X] => fx.asInstanceOf[F[∃[R]#S]] }
  }

}