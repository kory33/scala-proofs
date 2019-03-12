package com.github.kory33.proof.peano

import scala.reflect.Selectable.reflectiveSelectable

import com.github.kory33.proof.logic.propositional.LogicDefinitions._

import com.github.kory33.proof.peano.foundation._
import com.github.kory33.proof.function.ConstantFunction

trait Arithmetic {
  val context: ArithmeticContext
  implicit val axioms: Peano.Axioms { val context: Arithmetic.this.context.type }
  
  import context._
  import axioms._
  import Peano._

  type NWrap = nfn1.domCtx.OWrap
  type Succ[n] = S @: n

  type _0 = Zero
  type _1 = Succ[_0]
  type _2 = Succ[_1]

  val nfn1Const: ConstantFunction { val context: nfn1.type } = new ConstantFunction { val context: nfn1.type = nfn1 }
  import nfn1Const.{ Constant => Constant1, _ }

  val nfn2Const: ConstantFunction { val context: nfn2.type } = new ConstantFunction { val context: nfn2.type = nfn2 }
  import nfn2Const.{ Constant => Constant2, _ }

  implicit def succNat[n: Nat]: Nat[Succ[n]] = nfn1.application

  type Itr[init, f] = Rec[init, Constant2[f]]
  implicit def itrFunction[init: Nat, f: nfn1.Univ]: nfn1.Univ[Itr[init, f]] = primitiveRecursion
  implicit def itrEqZero[init: Nat, f: nfn1.Univ]: (Itr[init, f] @: _0) =::= init = implicitly
  implicit def itrEqSucc[init: Nat, f: nfn1.Univ, x: Nat]: (Itr[init, f] @: Succ[x]) =::= (f @: (Itr[init, f] @: x)) = {
    val ev1: nfn1.=::=[Constant2[f] :@@ x, f] = nfn2Const.constantApply[f, x]
    ev1.sub[[fn] => (Itr[init, f] @: Succ[x]) =::= (fn @: (Itr[init, f] @: x))](primitiveRecursionEqSucc)
  }

  type +[n, m] = Itr[n, S] @: m
  implicit def plusNat[n: Nat, m: Nat]: Nat[n + m] = nfn1.application

  val addRightUnit: ∀[[n] => (n + _0) =::= n] = new { def apply[n: Nat] = itrEqZero }
  val addSuccRight: ∀[[n] => ∀[[m] => (n + Succ[m]) =::= Succ[n + m]]] = new { def apply[n: Nat] = new { def apply[m: Nat] = itrEqSucc[n, S, m] } }

  val addLeftUnit: ∀[[n] => (_0 + n) =::= n] = {
    val inductionPart: ∀[[n] => ((_0 + n) =::= n) => ((_0 + Succ[n]) =::= Succ[n])] = new { def apply[n: Nat] = indHyp: ((_0 + n) =::= n) =>
      indHyp.sub[[zn] => (_0 + Succ[n]) =::= Succ[zn]](addSuccRight[_0][n])
    }
    induction(addRightUnit[_0], inductionPart)
  }

  val plusOneIsSucc: ∀[[n] => (n + _1) =::= Succ[n]] = new { def apply[n: Nat] = {
    val ev1: (n + _1) =::= Succ[n + _0] = addSuccRight[n][_0]
    val ev2: Succ[n + _0] =::= Succ[n] = addRightUnit[n].sub[[snz] => Succ[n + _0] =::= Succ[snz]](identityEquality)
    ev1.andThen(ev2)
  } }

  val addAssoc: ∀[[a] => ∀[[b] => ∀[[c] => ((a + b) + c) =::= (a + (b + c))]]] = new { def apply[a: Nat] = new { def apply[b: Nat] = {
    val zeroCaseC: ((a + b) + _0) =::= (a + (b + _0)) = {
      val ev1: ((a + b) + _0) =::= (a + b) = addRightUnit[a + b]
      val ev2: (a + b) =::= (a + (b + _0)) = addRightUnit[b].sub[[b0] => (a + b0) =::= (a + (b + _0))](identityEquality)
      ev1.andThen(ev2)
    }
    val inductionPartC: ∀[[c] => (((a + b) + c) =::= (a + (b + c))) => (((a + b) + Succ[c]) =::= (a + (b + Succ[c])))] = new { def apply[c: Nat] = {
      hypothesis: ((a + b) + c) =::= (a + (b + c)) => {
        val ev1: ((a + b) + Succ[c]) =::= Succ[(a + b) + c] = addSuccRight[a + b][c]
        val ev2: Succ[(a + b) + c] =::= Succ[a + (b + c)] = hypothesis.sub[[abc] => Succ[(a + b) + c] =::= Succ[abc]](identityEquality)
        val ev3: Succ[a + (b + c)] =::= (a + Succ[b + c]) = addSuccRight[a][b + c].commute
        val ev4: (a + Succ[b + c]) =::= (a + (b + Succ[c])) = addSuccRight[b][c].commute.sub[[bsc] => (a + Succ[b + c]) =::= (a + bsc)](identityEquality)
        ev1.andThen(ev2).andThen(ev3).andThen(ev4)
      }
    } }
    induction(zeroCaseC, inductionPartC)
  } } }

  val addSuccLeft: ∀[[n] => ∀[[m] => (Succ[n] + m) =::= Succ[n + m]]] = new { def apply[n: Nat] = new { def apply[m: Nat] = {
    val plusOneComm: ∀[[n] => (_1 + n) =::= (n + _1)] = {
      val zeroCase: (_1 + _0) =::= (_0 + _1) = addRightUnit[_1].andThen(addLeftUnit[_1].commute)
      val inductionPart: ∀[[n] => ((_1 + n) =::= (n + _1)) => ((_1 + Succ[n]) =::= (Succ[n] + _1))] = new { def apply[n: Nat] = hypothesis: ((_1 + n) =::= (n + _1)) => {
        val ev1: (_1 + Succ[n]) =::= (_1 + (n + _1)) = plusOneIsSucc[n].sub[[sn] => (_1 + sn) =::= (_1 + (n + _1))](identityEquality)
        val ev2: (_1 + (n + _1)) =::= ((_1 + n) + _1) = addAssoc[_1][n][_1].commute
        val ev3: ((_1 + n) + _1) =::= ((n + _1) + _1) = hypothesis.sub[[n1] => ((_1 + n) + _1) =::= (n1 + _1)](identityEquality)
        val ev4: ((n + _1) + _1) =::= (Succ[n] + _1) = plusOneIsSucc[n].sub[[sn] => ((n + _1) + _1) =::= (sn + _1)](identityEquality)

        ev1.andThen(ev2).andThen(ev3).andThen(ev4)
      } }
      induction(zeroCase, inductionPart)
    }

    val ev1: (Succ[n] + m) =::= ((n + _1) + m) = plusOneIsSucc[n].commute.sub[[sn] => (Succ[n] + m) =::= (sn + m)](identityEquality)
    val ev2: ((n + _1) + m) =::= ((_1 + n) + m) = plusOneComm[n].commute.sub[[op] => ((n + _1) + m) =::= (op + m)](identityEquality)
    val ev3: ((_1 + n) + m) =::= (_1 + (n + m)) = addAssoc[_1][n][m]
    val ev4: (_1 + (n + m)) =::= ((n + m) + _1) = plusOneComm[n + m]
    val ev5: ((n + m) + _1) =::= Succ[n + m] = plusOneIsSucc[n + m]

    ev1.andThen(ev2).andThen(ev3).andThen(ev4).andThen(ev5)
  } } }

  val addComm: ∀[[n] => ∀[[m] => (n + m) =::= (m + n)]] = {
    val zeroCaseN: ∀[[m] => (_0 + m) =::= (m + _0)] = new { def apply[m: Nat] = addLeftUnit[m].andThen(addRightUnit[m].commute) }
    val inductionPartN: ∀[[n] => ∀[[m] => (n + m) =::= (m + n)] => ∀[[m] => (Succ[n] + m) =::= (m + Succ[n])]] = new { def apply[n: Nat] = {
      indHypN: ∀[[m] => (n + m) =::= (m + n)] => new { def apply[m: Nat] = {
        val ev1: (Succ[n] + m) =::= Succ[n + m] = addSuccLeft[n][m]
        val ev2: Succ[n + m] =::= Succ[m + n] = indHypN[m].sub[[mn] => Succ[n + m] =::= Succ[mn]](identityEquality[Succ[n + m]])
        val ev3: Succ[m + n] =::= (m + Succ[n]) = addSuccRight[m][n].commute
        ev1.andThen(ev2).andThen(ev3)
      } }
    } }
    induction(zeroCaseN, inductionPartN)
  }

  val sumIdentThenZero: ∀[[x] => ∀[[n] => ((n + x) =::= n) => (x =::= _0)]] = {
    ???
  }

  val sumZeroThenBothZero: ∀[[a] => ∀[[b] => ((a + b) =::= _0) => (a =::= _0) ∧ (b =::= _0)]] = {
    ???
  }

  type ≦[n, m] = ∃[[x] => (n + x) =::= m]
  type ≧[n, m] = m ≦ n

  val leqRefl: ∀[[a] => a ≦ a] = new { def apply[a: Nat] = genExist(addRightUnit[a]) }

  val leqTrans: ∀[[a] => ∀[[b] => ∀[[c] => ((a ≦ b) ∧ (b ≦ c)) => (a ≦ c)]]] = new { def apply[a: Nat] = new { def apply[b: Nat] = new { def apply[c: Nat] = {
    hypothesis: ((a ≦ b) ∧ (b ≦ c)) => {
      implicit val ev1: ∃[[x] => (a + x) =::= b] = hypothesis._1
      implicit val ev2: ∃[[y] => (b + y) =::= c] = hypothesis._2
      type x = ev1.W; type y = ev2.W
      val ev3: (a + x) =::= b = ev1.proof
      val ev4: (b + y) =::= c = ev2.proof
      val ev5: ((a + x) + y) =::= c = ev3.commute.sub[[ax] => (ax + y) =::= c](ev4)
      val ev6: (a + (x + y)) =::= c = (addAssoc[a][x][y]).sub[[axy] => axy =::= c](ev5)
      genExist[[xy] => (a + xy) =::= c, x + y](ev6)
    }
  } } } }

  val leqAntisym: ∀[[a] => ∀[[b] => ((a ≦ b) ∧ (a ≧ b)) => (a =::= b)]] = new { def apply[a: Nat] = new { def apply[b: Nat] = {
    hypothesis: ((a ≦ b) ∧ (a ≧ b)) => {
      implicit val ev1: ∃[[t1] => (a + t1) =::= b] = hypothesis._1
      implicit val ev2: ∃[[t2] => (b + t2) =::= a] = hypothesis._2
      type t1 = ev1.W; type t2 = ev2.W
      val ev3: (a + t1) =::= b = ev1.proof
      val ev4: (b + t2) =::= a = ev2.proof
      val ev5: ((a + t1) + t2) =::= a = ev3.commute.sub[[at1] => (at1 + t2) =::= a](ev4)
      val ev6: (a + (t1 + t2)) =::= a = addAssoc[a][t1][t2].sub[[a12] => a12 =::= a](ev5)
      val ev7: (t1 + t2) =::= _0 = sumIdentThenZero[t1 + t2][a].apply(ev6)
      val ev8: (t1 =::= _0) ∧ (t2 =::= _0) = sumZeroThenBothZero[t1][t2].apply(ev7)
      val ev9: (a + _0) =::= b = ev8._1.sub[[z] => (a + z) =::= b](ev3)

      addRightUnit[a].sub[[a0] => a0 =::= b](ev9)
    }
  } } }

  type mult = λ2[[n] => λ1[[m] => Itr[_0, λ1[[x] => x + n]] @: m]]
  type *[n, m] = mult :@@ n @: m

  type expn = λ2[[n] => λ1[[m] => Itr[S @: _0, λ1[[x] => x * n]] @: m]]
  type ^[n, m] = expn :@@ n @: m

}
