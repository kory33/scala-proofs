package com.github.kory33.proof.set

import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateSystem._
import com.github.kory33.proof.set.logic._
import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.logic.propositional.ClassicalLogicSystem._
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set.ZFAxiom._

object Shortcuts {
  /**
   * shorthand for axiom schema of separation.
   */
  def separate[X <: Σ, F[_ <: Σ, _ <: Σ], A <: Σ](implicit axiom: ZFAxiom): ∃[[y <: Σ] => ∀[[u <: Σ] => (u ∈ y) <=> ((u ∈ X) ∧ F[u, A])]] =
    forType[A].instantiate[[p <: Σ] => ∃[[y <: Σ] => ∀[[u <: Σ] => (u ∈ y) <=> ((u ∈ X) ∧ F[u, p])]]](
      forType[X].instantiate[[x <: Σ] => ∀[[p <: Σ] => ∃[[y <: Σ] => ∀[[u <: Σ] => (u ∈ y) <=> ((u ∈ x) ∧ F[u, p])]]]](
        separation[F]
      )
    )

  /**
   * If there exists a set containing all set u such that F[u], then there exists a subset containing all u such that F[u] and nothing else.
   */
  def comprehendsExactly[F[_ <: Σ]](existsSuperSet: ∃[[y <: Σ] => ∀[[z <: Σ] => F[z] => (z ∈ y)]])(implicit axiom: ZFAxiom): ∃[[y <: Σ] => ∀[[z <: Σ] => (z ∈ y) <=> F[z]]] = {
    type Y = existsSuperSet.S
    val ev1: ∀[[u <: Σ] => F[u] => (u ∈ Y)] = existsSuperSet.value
    val ev2: ∃[[w <: Σ] => ∀[[u <: Σ] => (u ∈ w) <=> ((u ∈ Y) ∧ F[u])]] = separate[Y, [u <: Σ, _ <: Σ] => F[u], Y]
    type W = ev2.S
    val ev3: ∀[[u <: Σ] => (u ∈ W) <=> ((u ∈ Y) ∧ F[u])] = ev2.value
    val ev4: ∀[[u <: Σ] => (u ∈ W) <=> F[u]] = byContradiction { assumption: ∃[[u <: Σ] => ￢[(u ∈ W) <=> F[u]]] =>
      type U = assumption.S
      val ev41: ￢[(U ∈ W) <=> F[U]] = assumption.value
      val ev42: (U ∈ W) <=> ((U ∈ Y) ∧ F[U]) = forType[U].instantiate[[u <: Σ] => (u ∈ W) <=> ((u ∈ Y) ∧ F[u])](ev3)
      val ev43: (U ∈ W) => F[U] = ev42.implies.andThen(_._2)
      val ev44: F[U] => (U ∈ Y) = forType[U].instantiate[[u <: Σ] => F[u] => (u ∈ Y)](ev1)
      val ev45: F[U] => (U ∈ W) = { fu: F[U] => ev42.impliedBy(ev44(fu) ∧ fu) }
      val ev46: (U ∈ W) <=> F[U] = ev43 ∧ ev45
      ev46 ∧ ev41
    }
    forType[W].generalize[[y <: Σ] => ∀[[z <: Σ] => (z ∈ y) <=> F[z]]](ev4)
  }
  /**
   * shorthand for axiom of extensionality.
   */
  def setEquals[X <: Σ, Y <: Σ](containsSameElement: ∀[[z <: Σ] => (z ∈ X) <=> (z ∈ Y)])(implicit axiom: ZFAxiom): X =::= Y = {
    forType[Y].instantiate[[y <: Σ] => ∀[[z <: Σ] => (z ∈ X) <=> (z ∈ y)] => (X =::= y)](
      forType[X].instantiate[[x <: Σ] => ∀[[y <: Σ] => ∀[[z <: Σ] => (z ∈ x) <=> (z ∈ y)] => (x =::= y)]](extensionality)
    )(containsSameElement)
  }

  /**
   * creates a type-level function given the that the relation is a bijection on types.
   */
  def createTypeFunction[R[_ <: Σ, _ <: Σ]]
    (exists: ∀[[x <: Σ] => ∃[[y <: Σ] => y R x]],
     unique: ∀[[z <: Σ] => ∀[[x <: Σ] => ∀[[y <: Σ] => (x R z) ∧ (y R z) => x =::= y]]])
    : ∃~>[[TypeFunction[_ <: Σ] <: Σ] => ∀[[x <: Σ] => TypeFunction[x] R x]] = {
      new ∃~>[[TypeFunction[_ <: Σ] <: Σ] => ∀[[x <: Σ] => TypeFunction[x] R x]] {
        type F[x <: Σ] = ∃[[y <: Σ] => y R x]#S
        val value: ∀[[x <: Σ] => F[x] R x] = {
          byContradiction { assumption: ∃[[x <: Σ] => ￢[F[x] R x]] =>
            type X = assumption.S
            val ev1: ￢[F[X] R X] = assumption.value
            val ev2: ∃[[y <: Σ] => y R X] = forType[X].instantiate[[x <: Σ] => ∃[[y <: Σ] => y R x]](exists)
            val ev3: ev2.S R X = ev2.value
            // since the subtype of F[X] is unique to ev2.S, they are isomorphic.
            // it is therefore safe to cast from G[ev2.S] to G[F[X]] for any G[_].
            // let G[x] = x R X, then this cast is safe.
            val ev4: F[X] R X = ev3.asInstanceOf[F[X] R X]
            ev4 ∧ ev1
          }
        }
      }
    }
}

class PowerSet(implicit axiom: ZFAxiom) {
  import Shortcuts._

  /**
   * There exists a set containing all subsets of x and nothing else.
   */
  val powerSetExists: ∀[[x <: Σ] => ∃[[y <: Σ] => y isPowerOf x]] = {
    byContradiction { assumption: ∃[[x <: Σ] => ￢[∃[[y <: Σ] => y isPowerOf x]]] =>
      type X = assumption.S
      val ev1: ￢[∃[[y <: Σ] => y isPowerOf X]] = assumption.value
      val ev2: ∃[[y <: Σ] => ∀[[z <: Σ] => (z ⊂ X) => (z ∈ y)]] = forType[X].instantiate[[x <: Σ] => ∃[[p <: Σ] => ∀[[z <: Σ] => (z ⊂ x) => (z ∈ p)]]](power)
      val ev3: ∃[[y <: Σ] => ∀[[z <: Σ] => (z ∈ y) <=> (z ⊂ X)]] = comprehendsExactly[[z <: Σ] => z ⊂ X](ev2)
      val ev4: ∃[[y <: Σ] => y isPowerOf X] = ev3
      ev4 ∧ ev1
    }
  }

  /**
   * Power set is unique.
   */
  val powerSetUnique: ∀[[z <: Σ] => ∀[[x <: Σ] => ∀[[y <: Σ] => (x isPowerOf z) ∧ (y isPowerOf z) => x =::= y]]] = {
    byContradiction { assumption: ∃[[z <: Σ] => ￢[∀[[x <: Σ] => ∀[[y <: Σ] => (x isPowerOf z) ∧ (y isPowerOf z) => x =::= y]]]] =>
      type Z = assumption.S
      val ev1: ￢[∀[[x <: Σ] => ∀[[y <: Σ] => (x isPowerOf Z) ∧ (y isPowerOf Z) => x =::= y]]] = assumption.value
      val ev2: ∃[[x <: Σ] => ￢[∀[[y <: Σ] => (x isPowerOf Z) ∧ (y isPowerOf Z) => x =::= y]]] = ev1
      type X = ev2.S
      val ev3: ∃[[y <: Σ] => ￢[(X isPowerOf Z) ∧ (y isPowerOf Z) => X =::= y]] = ev2.value
      type Y = ev3.S
      val ev4: ￢[(X isPowerOf Z) ∧ (Y isPowerOf Z) => X =::= Y] = ev3.value
      val ev5: (X isPowerOf Z) ∧ (Y isPowerOf Z) => X =::= Y = { case (xIsPowerOfZ, yIsPowerOfZ) =>
        val ev51: ∀[[w <: Σ] => (w ∈ X) <=> (w ⊂ Z)] = xIsPowerOfZ
        val ev52: ∀[[w <: Σ] => (w ∈ Y) <=> (w ⊂ Z)] = yIsPowerOfZ
        val ev53: ∀[[w <: Σ] => (w ∈ X) <=> (w ∈ Y)] = byContradiction { assumption53: ∃[[w <: Σ] => ￢[(w ∈ X) <=> (w ∈ Y)]] =>
          type W = assumption53.S
          val ev531: ￢[(W ∈ X) <=> (W ∈ Y)] = assumption53.value
          val ev532: (W ∈ X) <=> (W ⊂ Z) = forType[W].instantiate[[w <: Σ] => (w ∈ X) <=> (w ⊂ Z)](ev51)
          val ev533: (W ∈ Y) <=> (W ⊂ Z) = forType[W].instantiate[[w <: Σ] => (w ∈ Y) <=> (w ⊂ Z)](ev52)
          val ev534: (W ∈ X) <=> (W ∈ Y) = ev532.andThen(ev533.commute)
          ev534 ∧ ev531
        }
        setEquals(ev53)
      }
      ev5 ∧ ev4
    }
  }

  val powerFunctionExists: ∃~>[[Pow[_ <: Σ] <: Σ] => ∀[[x <: Σ] => Pow[x] isPowerOf x]] = createTypeFunction[isPowerOf](powerSetExists, powerSetUnique)

  type Pow[x <: Σ] = powerFunctionExists.F[x]
  val powerSetConstraints: ∀[[x <: Σ] => Pow[x] isPowerOf x] = powerFunctionExists.value
}

class EmptySet(implicit axiom: ZFAxiom) {
  import Shortcuts._

  /**
    * There exists an empty set.
    */
  val emptySet: ∃[isEmpty] = {
    val set = existence

    type Set = set.S

    val emptyExistence: ∃[[y <: Σ] => ∀[[u <: Σ] => (u ∈ y) <=> ((u ∈ Set) ∧ Nothing)]] = separate[Set, [_, _] => Nothing, Set]

    type EmptySet = emptyExistence.S
    val ev1: ∀[[u <: Σ] => (u ∈ EmptySet) <=> ((u ∈ Set) ∧ Nothing)] = emptyExistence.value
    val ev2: ∀[[u <: Σ] => (u ∈ EmptySet) => Nothing] = byContradiction { assumption: ∃[[u <: Σ] => ￢[u ∈ EmptySet] => Nothing] =>
      type U = assumption.S
      val ev21 = assumption.value
      val ev22 = forType[U].instantiate[[u <: Σ] => (u ∈ EmptySet) <=> ((u ∈ Set) ∧ Nothing)](ev1)
      val ev23 = ev22.implies.andThen { conclusion: (U ∈ Set) ∧ Nothing => conclusion._2 }
      ev21(ev23)
    }
    val ev3: ∀[[u <: Σ] => u ∉ EmptySet] = ev2
  
    forType[EmptySet].generalize[[x <: Σ] => ∀[[y <: Σ] => y ∉ x]](ev3)
  }

  type ∅ = emptySet.S

  val emptyUnique: ∀[[x <: Σ] => isEmpty[x] => (x =::= ∅)] = {
    byContradiction { assumption: ∃[[x <: Σ] => ￢[isEmpty[x] => (x =::= ∅)]] =>
      type X = assumption.S
      val ev1: ￢[isEmpty[X] => (X =::= ∅)] = assumption.value
      val ev2: ∀[[z <: Σ] => (z ∈ X) <=> (z ∈ ∅)] => (X =::= ∅) =
        forType[∅].instantiate[[y <: Σ] => ∀[[z <: Σ] => (z ∈ X) <=> (z ∈ y)] => (X =::= y)](
          forType[X].instantiate[[x <: Σ] => ∀[[y <: Σ] => ∀[[z <: Σ] => (z ∈ x) <=> (z ∈ y)] => (x =::= y)]](extensionality)
        )
      val ev3: isEmpty[X] => ∀[[z <: Σ] => (z ∈ X) <=> (z ∈ ∅)] = { xIsEmpty: ∀[[y <: Σ] => y ∉ X] =>
        byContradiction { assumption3: ∃[[z <: Σ] => ￢[(z ∈ X) <=> (z ∈ ∅)]] =>
          type Z = assumption3.S
          val ev31: ￢[(Z ∈ X) <=> (Z ∈ ∅)] = assumption3.value
          val ev32: (Z ∈ X) => (Z ∈ ∅) = { assumption32: Z ∈ X =>
            assumption32 ∧ forType[Z].instantiate[[y <: Σ] => y ∉ X](xIsEmpty)
          }
          val ev33: (Z ∈ ∅) => (Z ∈ X) = { assumption33: Z ∈ ∅ =>
            assumption33 ∧ forType[Z].instantiate[[y <: Σ] => y ∉ ∅](emptySet.value)
          }
          val ev34: (Z ∈ X) <=> (Z ∈ ∅) = ev32 ∧ ev33
          ev34 ∧ ev31
        }
      }
      val ev4: isEmpty[X] => (X =::= ∅) = ev3.andThen(ev2)
      ev4 ∧ ev1
    }
  }
}

class BasicConstructs(implicit axiom: ZFAxiom) {
  import Shortcuts._

  /**
   * There is no set of all sets.
   */
  val noSetOfAllSets: ￢[∃[[x <: Σ] => ∀[[y <: Σ] => y ∈ x]]] = {
    def lemma1[A, B]: ￢[(A <=> (B ∧ ￢[A])) ∧ B] = byContradiction { assumption: (A <=> (B ∧ ￢[A])) ∧ B =>
      val (aEqBAndNotA, b) = assumption
      def ev1: ￢[A] => A = { notA: ￢[A] => aEqBAndNotA.impliedBy(b ∧ notA) }
      def ev2: A => ￢[A] = { a: A => aEqBAndNotA.implies(a)._2 }
      val notAEqNotA = byContradiction { aEqNotA: A <=> ￢[A] =>
        val notA = byContradiction { a: A => a ∧ aEqNotA.implies(a) }
        val a: A = aEqNotA.impliedBy(notA)
        a ∧ notA
      }
      notAEqNotA(ev2 ∧ ev1)
    }
  
    byContradiction { assumption: ∃[[x <: Σ] => ∀[[y <: Σ] => y ∈ x]] =>
      type S = assumption.S
      val setOfAllSets = assumption.value

      val paradoxicalExistence: ∃[[z <: Σ] => ∀[[u <: Σ] => (u ∈ z) <=> ((u ∈ S) ∧ (u ∉ u))]] = separate[S, [X <: Σ, _] => X ∉ X, S]
      type Z = paradoxicalExistence.S
      val paradoxicalSet: ∀[[u <: Σ] => (u ∈ Z) <=> ((u ∈ S) ∧ (u ∉ u))] = paradoxicalExistence.value
      val ev1: (Z ∈ Z) <=> ((Z ∈ S) ∧ (Z ∉ Z)) = forType[Z].instantiate[[u <: Σ] => (u ∈ Z) <=> ((u ∈ S) ∧ (u ∉ u))](paradoxicalSet)
      val ev2: Z ∈ S = forType[Z].instantiate[[y <: Σ] => y ∈ S](setOfAllSets)
      lemma1(ev1 ∧ ev2)
    }
  }

  val emptySet = new EmptySet
  type ∅ = emptySet.∅

  val powerSet = new PowerSet
  type Pow[x <: Σ] = powerSet.Pow
}
