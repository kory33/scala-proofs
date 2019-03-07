package com.github.kory33.proof.peano.foundation

import com.github.kory33.proof.logic.predicate._

import com.github.kory33.proof.function.foundation._

trait PeanoContext extends PredicateLogicContext {
  type Nat = Univ

  // "some" context on function whose domain and codomains are both naturals
  val natFuncCtx: EndoFunctionContext & MultiarityFunctionContext { type InCod = Nat; type InDom = Nat }

  // shorthand for natural function
  val nfn: natFuncCtx.type = natFuncCtx

  type S
  type Zero
}

trait ArithmeticContext extends PeanoContext {
  type Rec[_, _]

  val nfn1: natFuncCtx.type = natFuncCtx
  val nfn2 = nfn1.nextArity
  val nfn3 = nfn2.nextArity

  type @: = nfn1.$_:
  type :@@ = nfn2.$_:
  type :@@@ = nfn3.$_:

  type λ1 = nfn1.Lambda
  type λ2 = nfn2.Lambda
  type λ3 = nfn3.Lambda

  implicit def primitiveRecursion[init: Nat, f: nfn2.Univ]
    : nfn1.Univ[Rec[init, f]]

  implicit def primitiveRecursionEqZero[init: Nat, f: nfn2.Univ]
    : (Rec[init, f] @: Zero) =::= init

  implicit def primitiveRecursionEqSucc[init: Nat, f: nfn2.Univ, x: Nat]
    : (Rec[init, f] @: (S @: x)) =::= ((f :@@ x) @: (Rec[init, f] @: x))

}
