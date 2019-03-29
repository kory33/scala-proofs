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

  type NWrap = OWrap

  type _0 = Zero
  type _1 = S[_0]
  type _2 = S[_1]

  implicit def succNat[n: Nat]: Nat[S[n]] = succFn[n]

  type Itr[init, f[_]] = Rec[init, [n, m] => f[m]]
  implicit def constFunction[f[_]: Fn1]: Fn2[[n, m] => f[m]] = genUniv { nOWrap: OWrap => implicitly }
  implicit def itrFunction[init: Nat, f[_]: Fn1]: Fn1[Itr[init, f]] = primitiveRecursion
  implicit def itrEqZero[init: Nat, f[_]: Fn1]: Itr[init, f][_0] =::= init = primitiveRecursionEqZero
  implicit def itrEqS[init: Nat, f[_]: Fn1, x: Nat]: Itr[init, f][S[x]] =::= f[Itr[init, f][x]] = primitiveRecursionEqSucc

  type +[n, m] = Itr[n, S][m]
  type *[n, m] = Itr[_0, [x] => x + n][m]
  type ^[n, m] = Itr[_1, [x] => x * n][m]

  implicit def plusNat[n: Nat, m: Nat]: Nat[n + m] = itrFunction[n, S][m]

  val addRightUnit: ∀[[n] => (n + _0) =::= n] = new { def apply[n: Nat] = itrEqZero }
  val addSRight: ∀[[n] => ∀[[m] => (n + S[m]) =::= S[n + m]]] = new { def apply[n: Nat] = new { def apply[m: Nat] = itrEqS[n, S, m] } }

  val addLeftUnit: ∀[[n] => (_0 + n) =::= n] = {
    val inductionPart: ∀[[n] => ((_0 + n) =::= n) => ((_0 + S[n]) =::= S[n])] = new { def apply[n: Nat] = indHyp: ((_0 + n) =::= n) =>
      indHyp.sub[[zn] => (_0 + S[n]) =::= S[zn]](addSRight[_0][n])
    }
    induction(addRightUnit[_0], inductionPart)
  }

  val plusOneIsS: ∀[[n] => (n + _1) =::= S[n]] = new { def apply[n: Nat] = {
    val ev1: (n + _1) =::= S[n + _0] = addSRight[n][_0]
    val ev2: S[n + _0] =::= S[n] = addRightUnit[n].sub[[snz] => S[n + _0] =::= S[snz]](identityEquality)
    ev1.andThen(ev2)
  } }

  val addAssoc: ∀[[a] => ∀[[b] => ∀[[c] => ((a + b) + c) =::= (a + (b + c))]]] = new { def apply[a: Nat] = new { def apply[b: Nat] = {
    val zeroCaseC: ((a + b) + _0) =::= (a + (b + _0)) = {
      val ev1: ((a + b) + _0) =::= (a + b) = addRightUnit[a + b]
      val ev2: (a + b) =::= (a + (b + _0)) = addRightUnit[b].sub[[b0] => (a + b0) =::= (a + (b + _0))](identityEquality)
      ev1.andThen(ev2)
    }
    val inductionPartC: ∀[[c] => (((a + b) + c) =::= (a + (b + c))) => (((a + b) + S[c]) =::= (a + (b + S[c])))] = new { def apply[c: Nat] = {
      hypothesis: ((a + b) + c) =::= (a + (b + c)) => {
        val ev1: ((a + b) + S[c]) =::= S[(a + b) + c] = addSRight[a + b][c]
        val ev2: S[(a + b) + c] =::= S[a + (b + c)] = hypothesis.sub[[abc] => S[(a + b) + c] =::= S[abc]](identityEquality)
        val ev3: S[a + (b + c)] =::= (a + S[b + c]) = addSRight[a][b + c].commute
        val ev4: (a + S[b + c]) =::= (a + (b + S[c])) = addSRight[b][c].commute.sub[[bsc] => (a + S[b + c]) =::= (a + bsc)](identityEquality)
        ev1.andThen(ev2).andThen(ev3).andThen(ev4)
      }
    } }
    induction(zeroCaseC, inductionPartC)
  } } }

  val addSLeft: ∀[[n] => ∀[[m] => (S[n] + m) =::= S[n + m]]] = new { def apply[n: Nat] = new { def apply[m: Nat] = {
    val plusOneComm: ∀[[n] => (_1 + n) =::= (n + _1)] = {
      val zeroCase: (_1 + _0) =::= (_0 + _1) = addRightUnit[_1].andThen(addLeftUnit[_1].commute)
      val inductionPart: ∀[[n] => ((_1 + n) =::= (n + _1)) => ((_1 + S[n]) =::= (S[n] + _1))] = new { def apply[n: Nat] = hypothesis: ((_1 + n) =::= (n + _1)) => {
        val ev1: (_1 + S[n]) =::= (_1 + (n + _1)) = plusOneIsS[n].sub[[sn] => (_1 + sn) =::= (_1 + (n + _1))](identityEquality)
        val ev2: (_1 + (n + _1)) =::= ((_1 + n) + _1) = addAssoc[_1][n][_1].commute
        val ev3: ((_1 + n) + _1) =::= ((n + _1) + _1) = hypothesis.sub[[n1] => ((_1 + n) + _1) =::= (n1 + _1)](identityEquality)
        val ev4: ((n + _1) + _1) =::= (S[n] + _1) = plusOneIsS[n].sub[[sn] => ((n + _1) + _1) =::= (sn + _1)](identityEquality)

        ev1.andThen(ev2).andThen(ev3).andThen(ev4)
      } }
      induction(zeroCase, inductionPart)
    }

    val ev1: (S[n] + m) =::= ((n + _1) + m) = plusOneIsS[n].commute.sub[[sn] => (S[n] + m) =::= (sn + m)](identityEquality)
    val ev2: ((n + _1) + m) =::= ((_1 + n) + m) = plusOneComm[n].commute.sub[[op] => ((n + _1) + m) =::= (op + m)](identityEquality)
    val ev3: ((_1 + n) + m) =::= (_1 + (n + m)) = addAssoc[_1][n][m]
    val ev4: (_1 + (n + m)) =::= ((n + m) + _1) = plusOneComm[n + m]
    val ev5: ((n + m) + _1) =::= S[n + m] = plusOneIsS[n + m]

    ev1.andThen(ev2).andThen(ev3).andThen(ev4).andThen(ev5)
  } } }

  val addComm: ∀[[n] => ∀[[m] => (n + m) =::= (m + n)]] = {
    val zeroCaseN: ∀[[m] => (_0 + m) =::= (m + _0)] = new { def apply[m: Nat] = addLeftUnit[m].andThen(addRightUnit[m].commute) }
    val inductionPartN: ∀[[n] => ∀[[m] => (n + m) =::= (m + n)] => ∀[[m] => (S[n] + m) =::= (m + S[n])]] = new { def apply[n: Nat] = {
      indHypN: ∀[[m] => (n + m) =::= (m + n)] => new { def apply[m: Nat] = {
        val ev1: (S[n] + m) =::= S[n + m] = addSLeft[n][m]
        val ev2: S[n + m] =::= S[m + n] = indHypN[m].sub[[mn] => S[n + m] =::= S[mn]](identityEquality[S[n + m]])
        val ev3: S[m + n] =::= (m + S[n]) = addSRight[m][n].commute
        ev1.andThen(ev2).andThen(ev3)
      } }
    } }
    induction(zeroCaseN, inductionPartN)
  }

  val sumIdentThenZero: ∀[[x] => ∀[[n] => ((n + x) =::= n) => (x =::= _0)]] = new { def apply[x: Nat] = {
    val zeroCase: ((_0 + x) =::= _0) => (x =::= _0) = { hypothesis => addLeftUnit[x].sub[[x0] => x0 =::= _0](hypothesis) }
    val inductionPart: ∀[[n] => (((n + x) =::= n) => (x =::= _0)) => (((S[n] + x) =::= S[n]) => (x =::= _0))] = new { def apply[n: Nat] = {
      indHypothesis: (((n + x) =::= n) => (x =::= _0)) => hypothesis: ((S[n] + x) =::= S[n]) => {
        val ev1: S[n + x] =::= S[n] = addSLeft[n][x].sub[[snx] => snx =::= S[n]](hypothesis)
        val ev2: (n + x) =::= n = succInj[n + x][n].apply(ev1)
        indHypothesis(ev2)
      }
    } }
    induction(zeroCase, inductionPart)
  } }

  val sumZeroThenLeftZero: ∀[[a] => ∀[[b] => ((a + b) =::= _0) => (a =::= _0)]] = {
    val zeroCaseA: ∀[[b] => ((_0 + b) =::= _0) => (_0 =::= _0)] = new { def apply[b: Nat] = { _ => identityEquality } }
    val inductionPartA: ∀[[a] => ∀[[b] => ((a + b) =::= _0) => (a =::= _0)] => ∀[[b] => ((S[a] + b) =::= _0) => (S[a] =::= _0)]] = new { def apply[a: Nat] = {
      indHypothesis: ∀[[b] => ((a + b) =::= _0) => (a =::= _0)] => new { def apply[b: Nat] = { hypothesis: (S[a] + b) =::= _0 =>
        val ev1: S[a + b] =::= _0 = addSLeft[a][b].sub[[sab] => sab =::= _0](hypothesis)
        zeroFirst(genExist(ev1))
      } }
    } }
    induction(zeroCaseA, inductionPartA)
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
      val ev8: t1 =::= _0 = sumZeroThenLeftZero[t1][t2].apply(ev7)
      val ev9: (a + _0) =::= b = ev8.sub[[z] => (a + z) =::= b](ev3)

      addRightUnit[a].sub[[a0] => a0 =::= b](ev9)
    }
  } } }

  val zeroSmallest: ∀[[n] => _0 ≦ n] = new { def apply[n: Nat] = genExist(addLeftUnit[n]) }

}
