package com.github.kory33.proof.set.peano

import scala.language.implicitConversions

import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.logic.propositional.ClassicalLogicSystem._
import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateSystem._
import com.github.kory33.proof.set.logic._
import com.github.kory33.proof.logic.predicate.Equality._
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set.Universal._
import com.github.kory33.proof.set._
import com.github.kory33.proof.set.zf.operators.ComprehensionConstruct


class PeanoConstruct(comprehension: ComprehensionConstruct) {
  private type Comprehension = comprehension.Comprehension

  trait PeanoSystem[N : SetDomain, _0, S[_]] {

    type Nat[n] = n ∈ N

    //region minimum definition

    // zero(x) is an element of X
    implicit val zero: Nat[_0]

    // S is an endofunction on N
    implicit val function: ∀[[n] => Nat[n] => Nat[S[n]]]

    // zero is not in range of f
    val zeroHasNoPred: ￢[N hasSome ([n] => S[n] =::= _0)]

    // S is injective
    val injective: (N hasAll ([n] => N hasAll ([m] => (S[n] =::= S[m]) => (n =::= m))))
    
    // every subset of N that contains zero and is inductive equals N
    val subsetEqual: ∀[[A] => (A ⊂ N) => (_0 ∈ A) => (A hasAll ([a] => S[a] ∈ A)) => A =::= N]

    //endregion

    // function quantified by generics
    implicit def functionG[n : Nat]: Nat[S[n]] = forType[n].instantiate[[n] => Nat[n] => Nat[S[n]]](function)(implicitly[Nat[n]])

    def injectiveG[n : Nat, m : Nat](snsm: S[n] =::= S[m]): (n =::= m) = {
      val ev1 = forType[n].instantiate[[n] => Nat[n] => N hasAll ([m] => (S[n] =::= S[m]) => (n =::= m))](injective)(implicitly)
      val ev2 = forType[m].instantiate[[m] => Nat[m] => (S[n] =::= S[m]) => (n =::= m)](ev1)(implicitly)
      ev2(snsm)
    }

    // principle of mathematical induction
    def induction[P[_]]: P[_0] => (N hasAll ([n] => P[n] => P[S[n]])) => (N hasAll P) = { p0 => inductive =>
      import comprehension.comprehensionIsSet

      type A = Comprehension[N, P]
      val ev1: A ⊂ N = comprehension.subset
      val ev2: _0 ∈ A = comprehension.constraint2[N, P, _0].impliedBy(zero ∧ p0)
      val ev3: A hasAll ([a] => S[a] ∈ A) = byContradiction { implicit assumption3: ∃[[x] => ￢[(x ∈ A) => (S[x] ∈ A)]] =>
        type X = assumption3.S
        val ev31: ￢[(X ∈ A) => (S[X] ∈ A)] = assumption3.instance
        val ev32: (X ∈ A) => (S[X] ∈ A) = { xInA =>
          implicit val ev321: X ∈ N = ev1.containsElement(xInA)
          val ev322: P[X] = comprehension.constraint2[N, P, X].implies(xInA)._2
          val ev323: P[S[X]] = forType[X].instantiate[[n] => (n ∈ N) => P[n] => P[S[n]]](inductive)(ev321)(ev322)
          val ev324: Nat[S[X]] = functionG[X]
          comprehension.constraint2[N, P, S[X]].impliedBy(ev324 ∧ ev323)
        }
        ev32 ∧ ev31
      }
      val ev4: A =::= N = forType[A].instantiate[[a] => (a ⊂ N) => (_0 ∈ a) => (a hasAll ([a1] => S[a1] ∈ a)) => a =::= N](subsetEqual)(ev1)(ev2)(ev3)
      val ev5: A hasAll P = comprehension.hasAll[N, P]
      ev4.sub[[a] => a hasAll P](ev5)
    }

    // any natural number is either zero or has a unique predecessor
    val zeroOrHasPred: N hasAll ([n] => (n =::= _0) ∨ ∃![[y] => Nat[y] ∧ (n =::= S[y])]) = {
      type prop[n] = (n =::= _0) ∨ ∃![[y] => Nat[y] ∧ (n =::= S[y])]
      val ev1: prop[_0] = Left(implicitly[_0 =::= _0])
      val ev2: (N hasAll ([n] => prop[n] => prop[S[n]])) = byContradiction { implicit assumption2: ∃[[m] => ￢[Nat[m] => prop[m] => prop[S[m]]]] =>
        type M = assumption2.S
        val ev21: ￢[Nat[M] => prop[M] => prop[S[M]]] = assumption2.instance
        val ev22: Nat[M] => prop[M] => prop[S[M]] = implicit natM => propM => {
          val ev221: ∃[[y] => Nat[y] ∧ (S[M] =::= S[y])] = forType[M].generalize(natM ∧ implicitly[S[M] =::= S[M]])
          val ev222: ∀[[x] => ∀[[y] => ((Nat[x] ∧ (S[M] =::= S[x])) ∧ (Nat[y] ∧ (S[M] =::= S[y]))) => x =::= y]] = {
            byContradiction { assumption: ￢[∀[[x] => ∀[[y] => ((Nat[x] ∧ (S[M] =::= S[x])) ∧ (Nat[y] ∧ (S[M] =::= S[y]))) => x =::= y]]] =>
              val ev2221: ∃[[x] => ∃[[y] => ￢[((Nat[x] ∧ (S[M] =::= S[x])) ∧ (Nat[y] ∧ (S[M] =::= S[y]))) => x =::= y]]] = {
                notForall2[[x, y] => ((Nat[x] ∧ (S[M] =::= S[x])) ∧ (Nat[y] ∧ (S[M] =::= S[y]))) => x =::= y](assumption)
              }
              type X = ev2221.S; type Y = ev2221.instance.S
              val ev2222: ￢[((Nat[X] ∧ (S[M] =::= S[X])) ∧ (Nat[Y] ∧ (S[M] =::= S[Y]))) => X =::= Y] = ev2221.instance.instance
              val ev2223: ((Nat[X] ∧ (S[M] =::= S[X])) ∧ (Nat[Y] ∧ (S[M] =::= S[Y]))) => X =::= Y = { case (nxsmsx, nysmsy) =>
                implicit val natX = nxsmsx._1
                implicit val natY = nysmsy._1
                val smsx = nxsmsx._2
                val smsy = nysmsy._2
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

    sealed trait AdditiveNat[n : Nat] {
      type +[m]
    }

    final object Additive0 extends AdditiveNat[_0] {
      override type +[m] = m
    }

    final class AdditiveSuccNat[k : Nat] extends AdditiveNat[S[k]] {
      override type +[m] = S[AdditiveNat[k]# +[m]]
    }

    type +[a, b] = AdditiveNat[a]# + [b]

    def additionFunctional[n : Nat, m : Nat]: Nat[n + m] = {
      val ev1: (AdditiveNat[n]# + [m]) ∈ N = ???
      ev1
    }
  }
}
