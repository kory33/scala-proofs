package com.github.kory33.proof.peano.foundation

import com.github.kory33.proof.logic.predicate._

import com.github.kory33.proof.function.foundation._

trait PeanoContext extends PredicateLogicContext {
  // "some" context on function whose domain and codomains are both naturals
  val natFuncCtx: EndoFunctionContext & MultiarityFunctionContext { type InCod = Univ }

  // shorthand for natural function
  val nfn: natFuncCtx.type = natFuncCtx

  type S
  type Zero
}

trait ArithmeticContext extends PeanoContext {
  type Rec[_, _]

  val nfn1: nfn.type = nfn
  val nfn2 = nfn1.nextArity
  val nfn3 = nfn2.nextArity

  type @: = nfn1.$_:
  type :@@ = nfn2.$_:
  type :@@@ = nfn3.$_:

  type λ1 = nfn1.Lambda
  type λ2 = nfn2.Lambda
  type λ3 = nfn3.Lambda

  implicit def primitiveRecursive[init: Univ, f: nfn2.Univ]
    : nfn1.Univ[Rec[init, f]]

  implicit def primitiveRecursiveEqZero[init: Univ, f: nfn2.Univ]
    : (Rec[init, f] @: Zero) =::= init

  implicit def primitiveRecursiveEqSucc[init: Univ, f: nfn2.Univ, x: Univ]
    : (Rec[init, f] @: (S @: x)) =::= (f :@@ x @: (Rec[init, f] @: x))

  type Itr[init, f] = Rec[init, λ2[[x] => λ1[[m] => f @: m]]]

  type plus = λ2[[n] => λ1[[m] => Itr[n, S] @: m]]
  type +[n, m] = plus :@@ n @: m

  type mult = λ2[[n] => λ1[[m] => Itr[Zero, λ1[[x] => x + n]] @: m]]
  type *[n, m] = mult :@@ n @: m

  type expn = λ2[[n] => λ1[[m] => Itr[S @: Zero, λ1[[x] => x * n]] @: m]]
  type ^[n, m] = expn :@@ n @: m
}
