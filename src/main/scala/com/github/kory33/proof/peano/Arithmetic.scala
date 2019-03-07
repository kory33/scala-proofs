package com.github.kory33.proof.peano

import scala.reflect.Selectable.reflectiveSelectable

import com.github.kory33.proof.peano.foundation._
import com.github.kory33.proof.function.ConstantFunction

trait Arithmetic {
  val context: ArithmeticContext
  implicit val axioms: Peano.Axioms
  
  import context._
  import Peano._

  val nfn1Const: ConstantFunction { val context: nfn1.type } = new ConstantFunction { val context: nfn1.type = nfn1 }
  import nfn1Const.{ Constant => Constant1, _ }

  val nfn2Const: ConstantFunction { val context: nfn2.type } = new ConstantFunction { val context: nfn2.type = nfn2 }
  import nfn2Const.{ Constant => Constant2, _ }

  type Itr[init, f] = Rec[init, Constant2[f]]
  implicit def itrFunction[init: Nat, f: nfn1.Univ]: nfn1.Univ[Itr[init, f]] = primitiveRecursion
  implicit def itrEqZero[init: Nat, f: nfn1.Univ]: (Itr[init, f] @: Zero) =::= init = implicitly
  implicit def itrEqSucc[init: Nat, f: nfn1.Univ, x: Nat]: (Itr[init, f] @: (S @: x)) =::= (f @: (Itr[init, f] @: x)) = {
    val ev1: nfn1.=::=[Constant2[f] :@@ x, f] = nfn2Const.constantApply[f, x]
    ev1.sub[[fn] => (Itr[init, f] @: (S @: x)) =::= (fn @: (Itr[init, f] @: x))](primitiveRecursionEqSucc)
  }

  type plus = λ2[[n] => λ1[[m] => Itr[n, S] @: m]]
  type +[n, m] = plus :@@ n @: m

  type mult = λ2[[n] => λ1[[m] => Itr[Zero, λ1[[x] => x + n]] @: m]]
  type *[n, m] = mult :@@ n @: m

  type expn = λ2[[n] => λ1[[m] => Itr[S @: Zero, λ1[[x] => x * n]] @: m]]
  type ^[n, m] = expn :@@ n @: m

}
