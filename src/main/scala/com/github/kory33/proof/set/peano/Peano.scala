package com.github.kory33.proof.set.peano

import scala.language.implicitConversions

import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateSystem._
import com.github.kory33.proof.set.logic._
import com.github.kory33.proof.set.logic.Equality._
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set._
import com.github.kory33.proof.set.zf.RelationConstruct

trait PeanoSystem[N <: Σ, zero <: Σ, S[_ <: Σ] <: Σ] {

  // zero(x) is an element of X and not in range of f
  def zeroHasNoPred: (zero ∈ N) ∧ ￢[N hasSome ([n <: Σ] => S[n] =::= zero)]

  // f is an injective endofunction on X
  def injectiveFunction: (N hasAll ([n <: Σ] => S[n] ∈ N)) ∧ (N hasAll ([n <: Σ] => N hasAll ([m <: Σ] => (S[n] =::= S[m]) => (n =::= m))))
  
  // every subset of X satisfying 
  def subsetEqual: ∀[[A <: Σ] => (A ⊂ N) => (zero ∈ A) ∧ ∀[[a <: Σ] => a ∈ A => S[a] ∈ A] => A =::= N]

  // principle of mathematical induction
  def induction[P[_ <: Σ]]: P[zero] => (N hasAll ([n <: Σ] => P[n] => P[S[n]])) => (N hasAll P) = {
    // TODO prove this using subsetEqual
    ???
  }

  // any natural number is either zero or has predecessor
  def zeroOrHasPred: N hasAll ([n <: Σ] => (n =::= zero) ∨ ∃[[y <: Σ] => n =::= S[y]]) = {
    type prop[n <: Σ] = (n =::= zero) ∨ ∃[[y <: Σ] => n =::= S[y]]
    val ev1: prop[zero] = Left(implicitly[zero =::= zero])
    val ev2: (N hasAll ([n <: Σ] => prop[n] => prop[S[n]])) = byContradiction { assumption2: ∃[[m <: Σ] => ￢[(m ∈ N) => prop[m] => prop[S[m]]]] =>
      type M = assumption2.S
      val ev21: ￢[(M ∈ N) => prop[M] => prop[S[M]]] = assumption2.value
      val ev22: (M ∈ N) => prop[M] => prop[S[M]] = { _ => _ => Right(forType[M].generalize(implicitly[S[M] =::= S[M]])) }
      ev22 ∧ ev21
    }
    induction(ev1)(ev2)
  }

}
