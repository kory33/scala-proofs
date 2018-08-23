package com.github.kory33.proof.set.zf.constructs

import scala.language.implicitConversions

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.logic.propositional.ClassicalLogicSystem._
import com.github.kory33.proof.set.axiom.zf._
import com.github.kory33.proof.set.logic.Equality._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateSystem._
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set._

class OrderedPairConstruct(val singleton: SingletonConstruct)(implicit val axiom: ZFExtensionality) {

  type ++:[a <: Σ, b <: Σ] = singleton.pairSet.++:[a, b]
  type Just[a <: Σ] = singleton.Just[a]

  type :::[a <: Σ, b <: Σ] = Just[a] ++: (a ++: b)
  val constraintValue: ∀[[a <: Σ] => ∀[[b <: Σ] => ∀[[c <: Σ] => ∀[[d <: Σ] => ((a ::: b) =::= (c ::: d)) <=> ((a =::= c) ∧ (b =::= d))]]]] = {
    byContradiction { assumption: ￢[∀[[a <: Σ] => ∀[[b <: Σ] => ∀[[c <: Σ] => ∀[[d <: Σ] => ((a ::: b) =::= (c ::: d)) <=> ((a =::= c) ∧ (b =::= d))]]]]] =>
      val ev1: ∃[[a <: Σ] => ∃[[b <: Σ] => ∃[[c <: Σ] => ∃[[d <: Σ] => ￢[((a ::: b) =::= (c ::: d)) <=> ((a =::= c) ∧ (b =::= d))]]]]] = {
        notForall4[[a <: Σ, b <: Σ, c <: Σ, d <: Σ] => ((a ::: b) =::= (c ::: d)) <=> ((a =::= c) ∧ (b =::= d))](assumption)
      }
      type A = ev1.S; type B = ev1.value.S; type C = ev1.value.value.S; type D = ev1.value.value.value.S
      val ev2: ￢[((A ::: B) =::= (C ::: D)) <=> ((A =::= C) ∧ (B =::= D))] = ev1.value.value.value.value
      val ev3: ((A ::: B) =::= (C ::: D)) <=> ((A =::= C) ∧ (B =::= D)) = {
        val implies: ((A ::: B) =::= (C ::: D)) => ((A =::= C) ∧ (B =::= D)) = { abEqcd =>
          val ev31: A =::= C = {
            val ev311: (Just[A] =::= Just[C]) ∨ (Just[A] =::= (C ++: D)) = {
              val ev3111: containsTwo[A ::: B, Just[C], C ++: D] = abEqcd.commute.sub[[ab <: Σ] => containsTwo[ab, Just[C], C ++: D]](singleton.pairSet.constraint)
              val ev3112: Just[A] ∈ (A ::: B) = singleton.pairSet.containsLeft
              forType[Just[A]].instantiate[[w <: Σ] => (w ∈ (A ::: B)) <=> ((w =::= Just[C]) ∨ (w =::= (C ++: D)))](ev3111).implies(ev3112)
            }
            val ev312: (Just[A] =::= Just[C]) => (A =::= C) = singleton.equality
            val ev313: (Just[A] =::= (C ++: D)) => (A =::= C) = { assumption313 =>
              val ev3131: containsTwo[Just[A], C, D] = assumption313.commute.sub[[a <: Σ] => containsTwo[a, C, D]](singleton.pairSet.constraint)
              val ev3132: (C ∈ Just[A]) <=> ((C =::= C) ∨ (C =::= D)) = forType[C].instantiate[[w <: Σ] => (w ∈ Just[A]) <=> ((w =::= C) ∨ (w =::= D))](ev3131)
              val ev3133: C ∈ Just[A] = ev3132.impliedBy(Left(implicitly[C =::= C]))
              forType[C].instantiate[[z <: Σ] => (z ∈ Just[A]) <=> (z =::= A)](singleton.constraint).implies(ev3133).commute
            }
            removeDisj(ev311)(ev312)(ev313)
          }
          val ev32: B =::= D = {
            val ev331: (A ::: B) =::= (A ::: D) = ev31.commute.sub[[a <: Σ] => (A ::: B) =::= (a ::: D)](abEqcd)
            val ev332: ((A ++: B) =::= Just[A]) ∨ ((A ++: B) =::= (A ++: D)) = {
              val ev3322: (A ++: B) ∈ (A ::: D) = ev331.sub[[ad <: Σ] => (A ++: B) ∈ ad](singleton.pairSet.containsRight)
              forType[A ++: B].instantiate[[w <: Σ] => (w ∈ (A ::: D)) <=> ((w =::= Just[A]) ∨ (w =::= (A ++: D)))](singleton.pairSet.constraint).implies(ev3322)
            }
            val ev333: ((A ++: B) =::= (A ++: D)) => (B =::= D) = { assumption333 =>
              val ev3331: (B =::= A) ∨ (B =::= D) = {
                val ev33311: containsTwo[A ++: B, A, D] = assumption333.commute.sub[[ab <: Σ] => containsTwo[ab, A, D]](singleton.pairSet.constraint)
                forType[B].instantiate[[w <: Σ] => (w ∈ (A ++: B)) <=> ((w =::= A) ∨ (w =::= D))](ev33311).implies(singleton.pairSet.containsRight)
              }
              val ev3332: (B =::= A) => (B =::= D) = { assumption3332 =>
                val ev33321: Just[A] =::= (A ++: D) = assumption3332.sub[[a <: Σ] => (A ++: a) =::= (A ++: D)](assumption333)
                val ev33322: D ∈ Just[A] = ev33321.commute.sub[[ja <: Σ] => D ∈ ja](singleton.pairSet.containsRight[A, D])
                assumption3332.andThen(singleton.equalIfContained[D, A](ev33322).commute)
              }
              removeDisj(ev3331)(ev3332)(identity)
            }
            val ev334: ((A ++: B) =::= Just[A]) => (B =::= D) = { assumption334 =>
              val ev3341: B ∈ (A ++: B) = singleton.pairSet.containsRight[A, B]
              val ev3342: B =::= A = singleton.equalIfContained(assumption334.sub[[ja <: Σ] => B ∈ ja](ev3341))
              val ev3343: Just[Just[A]] =::= (A ::: D) = ev3342.sub[[a <: Σ] => (A ::: a) =::= (A ::: D)](ev331)
              val ev3344: (A ++: D) ∈ Just[Just[A]] = ev3343.commute.sub[[jja <: Σ] => (A ++: D) ∈ jja](singleton.pairSet.containsRight[Just[A], A ++: D])
              val ev3345: (A ++: D) =::= Just[A] = singleton.equalIfContained(ev3344)
              val ev3346: D ∈ Just[A] = ev3345.sub[[ja <: Σ] => D ∈ ja](singleton.pairSet.containsRight[A, D])
              ev3342.andThen(singleton.equalIfContained(ev3346).commute)
            }
            removeDisj(ev332)(ev334)(ev333)
          }
          ev31 ∧ ev32
        }
        val impliedBy: ((A =::= C) ∧ (B =::= D)) => ((A ::: B) =::= (C ::: D)) = { case (aEqC, bEqD) =>
          val ev31: (A ::: B) =::= (A ::: B) = implicitly[(A ::: B) =::= (A ::: B)]
          val ev32: (A ::: B) =::= (C ::: B) = aEqC.sub[[c <: Σ] => (A ::: B) =::= (c ::: B)](ev31)
          val ev33: (A ::: B) =::= (C ::: D) = bEqD.sub[[d <: Σ] => (A ::: B) =::= (C ::: d)](ev32)
          ev33
        }
        implies ∧ impliedBy
      }
      ev3 ∧ ev2
    }
  }

  def constraint[a <: Σ, b <: Σ, c <: Σ, d <: Σ]: ((a ::: b) =::= (c ::: d)) <=> ((a =::= c) ∧ (b =::= d)) = {
    forType2[c, d].instantiate[[c1 <: Σ, d1 <: Σ] => ((a ::: b) =::= (c1 ::: d1)) <=> ((a =::= c1) ∧ (b =::= d1))](
      forType2[a, b].instantiate[[a1 <: Σ, b1 <: Σ] => ∀[[c1 <: Σ] => ∀[[d1 <: Σ] => ((a1 ::: b1) =::= (c1 ::: d1)) <=> ((a1 =::= c1) ∧ (b1 =::= d1))]]](
        constraintValue
      )
    )
  }

}
