package com.github.kory33.proof.set.zf.operators

import scala.language.implicitConversions

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.logic.propositional.ClassicalLogicSystem._
import com.github.kory33.proof.set.axiom.zf._
import com.github.kory33.proof.set.logic.SetDomain
import com.github.kory33.proof.logic.predicate.Equality._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateSystem._
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set._

class OrderedPairConstruct(val singleton: SingletonConstruct)(implicit val axiom: ZFExtensionality) {

  val pairSet: singleton.pairSet.type = singleton.pairSet

  import pairSet.pairIsSet

  type ++:[a, b] = pairSet.++:[a, b]
  type Just[a] = singleton.Just[a]

  type :::[a, b] = Just[a] ++: (a ++: b)
  val constraintValue: ∀[[a] => ∀[[b] => ∀[[c] => ∀[[d] => ((a ::: b) =::= (c ::: d)) <=> ((a =::= c) ∧ (b =::= d))]]]] = {
    import pairSet.pairIsSet

    byContradiction { assumption: ￢[∀[[a] => ∀[[b] => ∀[[c] => ∀[[d] => ((a ::: b) =::= (c ::: d)) <=> ((a =::= c) ∧ (b =::= d))]]]]] =>
      implicit val ev1: ∃[[a] => ∃[[b] => ∃[[c] => ∃[[d] => ￢[((a ::: b) =::= (c ::: d)) <=> ((a =::= c) ∧ (b =::= d))]]]]] = {
        notForall4[[a, b, c, d] => ((a ::: b) =::= (c ::: d)) <=> ((a =::= c) ∧ (b =::= d))](assumption)
      }
      type A = ev1.S
      implicit val ev11 = ev1.instance
      type B = ev11.S
      implicit val ev12 = ev11.instance
      type C = ev12.S
      implicit val ev13 = ev12.instance
      type D = ev13.S
      val ev2: ￢[((A ::: B) =::= (C ::: D)) <=> ((A =::= C) ∧ (B =::= D))] = ev13.instance
      val ev3: ((A ::: B) =::= (C ::: D)) <=> ((A =::= C) ∧ (B =::= D)) = {
        val implies: ((A ::: B) =::= (C ::: D)) => ((A =::= C) ∧ (B =::= D)) = { abEqcd =>
          val ev31: A =::= C = {
            val ev311: (Just[A] =::= Just[C]) ∨ (Just[A] =::= (C ++: D)) = {
              pairSet.constraint2[Just[A], Just[C], C ++: D].implies(abEqcd.sub[[cd] => Just[A] ∈ cd](pairSet.containsLeft))
            }
            val ev312: (Just[A] =::= Just[C]) => (A =::= C) = singleton.equality
            val ev313: (Just[A] =::= (C ++: D)) => (A =::= C) = { assumption313 =>
              singleton.equalIfContained[C, A](assumption313.commute.sub[[ja] => C ∈ ja](pairSet.containsLeft)).commute
            }
            removeDisj(ev311)(ev312)(ev313)
          }
          val ev32: B =::= D = {
            val ev331: (A ::: B) =::= (A ::: D) = ev31.commute.sub[[a] => (A ::: B) =::= (a ::: D)](abEqcd)
            val ev332: ((A ++: B) =::= Just[A]) ∨ ((A ++: B) =::= (A ++: D)) = {
              pairSet.constraint2[A ++: B, Just[A], A ++: D].implies(ev331.sub[[ad] => (A ++: B) ∈ ad](pairSet.containsRight))
            }
            val ev333: ((A ++: B) =::= (A ++: D)) => (B =::= D) = { assumption333 =>
              val ev3331: (B =::= A) ∨ (B =::= D) = {
                pairSet.constraint2[B, A, D].implies(assumption333.sub[[ad] => B ∈ ad](pairSet.containsRight))
              }
              val ev3332: (B =::= A) => (B =::= D) = { assumption3332 =>
                val ev33321: Just[A] =::= (A ++: D) = assumption3332.sub[[a] => (A ++: a) =::= (A ++: D)](assumption333)
                val ev33322: D ∈ Just[A] = ev33321.commute.sub[[ja] => D ∈ ja](pairSet.containsRight[A, D])
                assumption3332.andThen(singleton.equalIfContained[D, A](ev33322).commute)
              }
              removeDisj(ev3331)(ev3332)(identity)
            }
            val ev334: ((A ++: B) =::= Just[A]) => (B =::= D) = { assumption334 =>
              val ev3342: B =::= A = singleton.equalIfContained(assumption334.sub[[ja] => B ∈ ja](pairSet.containsRight[A, B]))
              val ev3343: Just[Just[A]] =::= (A ::: D) = ev3342.sub[[a] => (A ::: a) =::= (A ::: D)](ev331)
              val ev3344: (A ++: D) ∈ Just[Just[A]] = ev3343.commute.sub[[jja] => (A ++: D) ∈ jja](pairSet.containsRight)
              val ev3345: (A ++: D) =::= Just[A] = singleton.equalIfContained(ev3344)
              val ev3346: D ∈ Just[A] = ev3345.sub[[ja] => D ∈ ja](pairSet.containsRight[A, D])
              ev3342.andThen(singleton.equalIfContained[D, A](ev3346).commute)
            }
            removeDisj(ev332)(ev334)(ev333)
          }
          ev31 ∧ ev32
        }
        val impliedBy: ((A =::= C) ∧ (B =::= D)) => ((A ::: B) =::= (C ::: D)) = { case (aEqC, bEqD) =>
          val ev31: (A ::: B) =::= (A ::: B) = implicitly[(A ::: B) =::= (A ::: B)]
          val ev32: (A ::: B) =::= (C ::: B) = aEqC.sub[[c] => (A ::: B) =::= (c ::: B)](ev31)
          val ev33: (A ::: B) =::= (C ::: D) = bEqD.sub[[d] => (A ::: B) =::= (C ::: d)](ev32)
          ev33
        }
        implies ∧ impliedBy
      }
      ev3 ∧ ev2
    }
  }

  implicit def setDomain[a : SetDomain, b : SetDomain]: SetDomain[a ::: b] = pairSet.pairIsSet

  def constraint[a : SetDomain, b : SetDomain, c : SetDomain, d : SetDomain]: ((a ::: b) =::= (c ::: d)) <=> ((a =::= c) ∧ (b =::= d)) = {
    forType2[c, d].instantiate[[c1, d1] => ((a ::: b) =::= (c1 ::: d1)) <=> ((a =::= c1) ∧ (b =::= d1))](
      forType2[a, b].instantiate[[a1, b1] => ∀[[c1] => ∀[[d1] => ((a1 ::: b1) =::= (c1 ::: d1)) <=> ((a1 =::= c1) ∧ (b1 =::= d1))]]](
        constraintValue
      )
    )
  }

}
