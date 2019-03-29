package com.github.kory33.proof.peano.foundation

import com.github.kory33.proof.logic.predicate._

import com.github.kory33.proof.function.foundation._

trait PeanoContext extends PredicateLogicContext {
  type Nat = Univ

  type Fn1[F[_]] = ∀[[n] => Univ[F[n]]]
  type Fn2[F[_, _]] = ∀[[n1] => ∀[[n2] => Univ[F[n1, n2]]]]

  type S[_]
  type Zero
}

trait ArithmeticContext extends PeanoContext {
  type RecUncurried[_, _[_, _], _]
  type Rec[init, f[_, _]] = [n] => RecUncurried[init, f, n]

  implicit def primitiveRecursion[init: Nat, f[_, _]: Fn2]: Fn1[Rec[init, f]]
  implicit def primitiveRecursionEqZero[init: Nat, f[_, _]: Fn2]: (Rec[init, f][Zero]) =::= init
  implicit def primitiveRecursionEqSucc[init: Nat, f[_, _]: Fn2, x: Nat]: (Rec[init, f][S[x]] =::= f[x, Rec[init, f][x]])

}
