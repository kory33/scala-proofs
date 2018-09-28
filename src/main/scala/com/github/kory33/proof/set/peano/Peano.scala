package com.github.kory33.proof.set.peano

import scala.language.implicitConversions

import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.logic.propositional.ClassicalLogicSystem._
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

    /**
     * Contextual typeclass for types being a natural number
     */
    type Nat[n <: Σ] = n ∈ N

    //region minimum definition

    // zero(x) is an element of X
    implicit val zero: Nat[_0]

    // S is an endofunction on N
    implicit val function: ∀[[n <: Σ] => Nat[n] => Nat[S[n]]]

    // zero is not in range of f
    val zeroHasNoPred: ￢[N hasSome ([n <: Σ] => S[n] =::= _0)]

    // S is injective
    val injective: (N hasAll ([n <: Σ] => N hasAll ([m <: Σ] => (S[n] =::= S[m]) => (n =::= m))))
    
    // every subset of N that contains zero and is inductive equals N
    val subsetEqual: ∀[[A <: Σ] => (A ⊂ N) => (_0 ∈ A) => (A hasAll ([a <: Σ] => S[a] ∈ A)) => A =::= N]

    //endregion

    // function quantified by generics
    implicit def functionG[n <: Σ : Nat]: Nat[S[n]] = forType[n].instantiate[[n <: Σ] => Nat[n] => Nat[S[n]]](function)(implicitly[Nat[n]])

    def injectiveG[n <: Σ : Nat, m <: Σ : Nat](snsm: S[n] =::= S[m]): (n =::= m) = {
      val ev1 = forType[n].instantiate[[n <: Σ] => Nat[n] => N hasAll ([m <: Σ] => (S[n] =::= S[m]) => (n =::= m))](injective)(implicitly)
      val ev2 = forType[m].instantiate[[m <: Σ] => Nat[m] => (S[n] =::= S[m]) => (n =::= m)](ev1)(implicitly)
      ev2(snsm)
    }

    // principle of mathematical induction
    def induction[P[_ <: Σ]]: P[_0] => (N hasAll ([n <: Σ] => P[n] => P[S[n]])) => (N hasAll P) = { p0 => inductive =>
      type A = Comprehension[N, P]
      val ev1: A ⊂ N = comprehension.subset
      val ev2: _0 ∈ A = comprehension.constraint2[N, P, _0].impliedBy(zero ∧ p0)
      val ev3: A hasAll ([a <: Σ] => S[a] ∈ A) = byContradiction { assumption3: ∃[[x <: Σ] => ￢[(x ∈ A) => (S[x] ∈ A)]] =>
        type X = assumption3.S
        val ev31: ￢[(X ∈ A) => (S[X] ∈ A)] = assumption3.value
        val ev32: (X ∈ A) => (S[X] ∈ A) = { xInA =>
          implicit val ev321: X ∈ N = ev1.containsElement(xInA)
          val ev322: P[X] = comprehension.constraint2[N, P, X].implies(xInA)._2
          val ev323: P[S[X]] = forType[X].instantiate[[n <: Σ] => (n ∈ N) => P[n] => P[S[n]]](inductive)(ev321)(ev322)
          val ev324: Nat[S[X]] = functionG[X]
          comprehension.constraint2[N, P, S[X]].impliedBy(ev324 ∧ ev323)
        }
        ev32 ∧ ev31
      }
      val ev4: A =::= N = forType[A].instantiate[[a <: Σ] => (a ⊂ N) => (_0 ∈ a) => (a hasAll ([a1 <: Σ] => S[a1] ∈ a)) => a =::= N](subsetEqual)(ev1)(ev2)(ev3)
      val ev5: A hasAll P = comprehension.hasAll[N, P]
      ev4.sub[[a <: Σ] => a hasAll P](ev5)
    }

    val natSuccThenNat: ∀[[n <: Σ] => Nat[S[n]] => Nat[n]] = byContradiction { assumption: ∃[[n <: Σ] => ￢[Nat[S[n]] => Nat[n]]] =>
      type N = assumption.S
      val ev1: ￢[Nat[S[N]] => Nat[N]] = assumption.value
      val ev2: Nat[S[N]] => Nat[N] = { natSN =>
        ???
      }
      ev2 ∧ ev1
    }

    def natSuccThenNatG[n <: Σ]: Nat[S[n]] => Nat[n] = forType[n].instantiate[[n <: Σ] => Nat[S[n]] => Nat[n]](natSuccThenNat)

    // any natural number is either zero or has a unique predecessor
    val zeroOrHasPred: N hasAll ([n <: Σ] => (n =::= _0) ∨ ∃![[y <: Σ] => n =::= S[y]]) = {
      type prop[n <: Σ] = (n =::= _0) ∨ ∃![[y <: Σ] => n =::= S[y]]
      val ev1: prop[_0] = Left(implicitly[_0 =::= _0])
      val ev2: (N hasAll ([n <: Σ] => prop[n] => prop[S[n]])) = byContradiction { assumption2: ∃[[m <: Σ] => ￢[Nat[m] => prop[m] => prop[S[m]]]] =>
        type M = assumption2.S
        val ev21: ￢[Nat[M] => prop[M] => prop[S[M]]] = assumption2.value
        val ev22: Nat[M] => prop[M] => prop[S[M]] = implicit natM => propM => {
          val ev221: ∃[[y <: Σ] => S[M] =::= S[y]] = forType[M].generalize(implicitly[S[M] =::= S[M]])
          val ev222: ∀[[x <: Σ] => ∀[[y <: Σ] => ((S[M] =::= S[x]) ∧ (S[M] =::= S[y])) => x =::= y]] = {
            byContradiction { assumption: ￢[∀[[x <: Σ] => ∀[[y <: Σ] => ((S[M] =::= S[x]) ∧ (S[M] =::= S[y])) => x =::= y]]] =>
              val ev2221: ∃[[x <: Σ] => ∃[[y <: Σ] => ￢[((S[M] =::= S[x]) ∧ (S[M] =::= S[y])) => x =::= y]]] = {
                notForall2[[x <: Σ, y <: Σ] => ((S[M] =::= S[x]) ∧ (S[M] =::= S[y])) => x =::= y](assumption)
              }
              type X = ev2221.S; type Y = ev2221.value.S
              val ev2222: ￢[((S[M] =::= S[X]) ∧ (S[M] =::= S[Y])) => X =::= Y] = ev2221.value.value
              val ev2223: ((S[M] =::= S[X]) ∧ (S[M] =::= S[Y])) => X =::= Y = { case (smsx, smsy) =>
                val ev22231: Nat[S[X]] = smsx.sub[[sx <: Σ] => Nat[sx]](functionG[M])
                val ev22232: Nat[S[Y]] = smsy.sub[[sy <: Σ] => Nat[sy]](functionG[M])
                implicit val natX: Nat[X] = natSuccThenNatG[X](ev22231)
                implicit val natY: Nat[Y] = natSuccThenNatG[Y](ev22232)
                injectiveG[X, Y](smsx.commute.andThen(smsy))
              }
              ev2223 ∧ ev2222
            }
          }
          Right(ev221 ∧ ev222)
        }
        ev22 ∧ ev21
      }
      induction(ev1)(ev2)
    }

/*
    sealed trait AdditiveNat[n <: Σ : Nat] {
      type +[m <: Σ] <: Σ
    }

    final object Additive0 extends AdditiveNat[_0] {
      override type +[m <: Σ] = m
    }

    final class AdditiveSuccNat[k <: Σ : Nat] extends AdditiveNat[S[k]] {
      override type +[m <: Σ] = S[AdditiveNat[k]# +[m]]
    }

    type +[a <: Σ, b <: Σ] = AdditiveNat[a]# + [b]

    def additionFunctional[n <: Σ : Nat, m <: Σ : Nat]: Nat[n + m] = {
      val ev1: (AdditiveNat[n]# + [m]) ∈ N = ???
      ev1
    }*/
  }
}
