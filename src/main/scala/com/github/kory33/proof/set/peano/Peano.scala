package com.github.kory33.proof.set.peano

import scala.language.implicitConversions

import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateSystem._
import com.github.kory33.proof.set.logic._
import com.github.kory33.proof.set.logic.Equality._
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set.Universal._
import com.github.kory33.proof.set._
import com.github.kory33.proof.set.zf.operators.ComprehensionConstruct

class PeanoConstruct(comprehension: ComprehensionConstruct) {
  private type Comprehension = comprehension.Comprehension

  trait PeanoSystem[N <: Σ, _0 <: Σ, S[_ <: Σ] <: Σ] {

    // zero(x) is an element of X
    val zeroIsInN: _0 ∈ N

    // zero is not in range of f
    val zeroHasNoPred: ￢[N hasSome ([n <: Σ] => S[n] =::= _0)]

    // S is an endofunction on N
    val function: N hasAll ([n <: Σ] => S[n] ∈ N)

    // S is injective
    val injective: (N hasAll ([n <: Σ] => N hasAll ([m <: Σ] => (S[n] =::= S[m]) => (n =::= m))))
    
    // every subset of N that contains zero and is inductive equals N
    val subsetEqual: ∀[[A <: Σ] => (A ⊂ N) => (_0 ∈ A) => (A hasAll ([a <: Σ] => S[a] ∈ A)) => A =::= N]

    // principle of mathematical induction
    def induction[P[_ <: Σ]]: P[_0] => (N hasAll ([n <: Σ] => P[n] => P[S[n]])) => (N hasAll P) = { p0 => inductive =>
      type A = Comprehension[N, P]
      val ev1: A ⊂ N = comprehension.subset
      val ev2: _0 ∈ A = comprehension.constraint2[N, P, _0].impliedBy(zeroIsInN ∧ p0)
      val ev3: A hasAll ([a <: Σ] => S[a] ∈ A) = byContradiction { assumption3: ∃[[x <: Σ] => ￢[(x ∈ A) => (S[x] ∈ A)]] =>
        type X = assumption3.S
        val ev31: ￢[(X ∈ A) => (S[X] ∈ A)] = assumption3.value
        val ev32: (X ∈ A) => (S[X] ∈ A) = { xInA =>
          val ev321: X ∈ N = ev1.containsElement(xInA)
          val ev322: P[X] = comprehension.constraint2[N, P, X].implies(xInA)._2
          val ev323: P[S[X]] = forType[X].instantiate[[n <: Σ] => (n ∈ N) => P[n] => P[S[n]]](inductive)(ev321)(ev322)
          val ev324: S[X] ∈ N = forType[X].instantiate[[n <: Σ] => (n ∈ N) => (S[n] ∈ N)](function)(ev321)
          comprehension.constraint2[N, P, S[X]].impliedBy(ev324 ∧ ev323)
        }
        ev32 ∧ ev31
      }
      val ev4: A =::= N = forType[A].instantiate[[a <: Σ] => (a ⊂ N) => (_0 ∈ a) => (a hasAll ([a1 <: Σ] => S[a1] ∈ a)) => a =::= N](subsetEqual)(ev1)(ev2)(ev3)
      val ev5: A hasAll P = comprehension.hasAll[N, P]
      ev4.sub[[a <: Σ] => a hasAll P](ev5)
    }

    // any natural number is either zero or has a predecessor
    val zeroOrHasPred: N hasAll ([n <: Σ] => (n =::= _0) ∨ ∃[[y <: Σ] => n =::= S[y]]) = {
      type prop[n <: Σ] = (n =::= _0) ∨ ∃[[y <: Σ] => n =::= S[y]]
      val ev1: prop[_0] = Left(implicitly[_0 =::= _0])
      val ev2: (N hasAll ([n <: Σ] => prop[n] => prop[S[n]])) = byContradiction { assumption2: ∃[[m <: Σ] => ￢[(m ∈ N) => prop[m] => prop[S[m]]]] =>
        type M = assumption2.S
        val ev21: ￢[(M ∈ N) => prop[M] => prop[S[M]]] = assumption2.value
        val ev22: (M ∈ N) => prop[M] => prop[S[M]] = { _ => _ => Right(forType[M].generalize(implicitly[S[M] =::= S[M]])) }
        ev22 ∧ ev21
      }
      induction(ev1)(ev2)
    }
  }
}