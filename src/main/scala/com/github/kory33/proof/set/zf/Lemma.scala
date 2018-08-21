package com.github.kory33.proof.set.zf

import scala.language.implicitConversions

import com.github.kory33.proof.meta.set.Isomorphisms

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.logic.propositional.ClassicalLogicSystem._
import com.github.kory33.proof.set.axiom.ZFAxiom
import com.github.kory33.proof.set.axiom.zf._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateSystem._
import com.github.kory33.proof.set.logic.Equality._
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set._

object Lemma {

  object Predicate {
    def forallConj[F[_ <: Σ], G[_ <: Σ]]: (∀[F] ∧ ∀[G]) <=> ∀[[x <: Σ] => F[x] ∧ G[x]] = {
      val implies: (∀[F] ∧ ∀[G]) => ∀[[x <: Σ] => F[x] ∧ G[x]] = { case (forallF, forallG) =>
        byContradiction { assumption: ∃[[x <: Σ] => ￢[F[x] ∧ G[x]]] =>
          type X = assumption.S
          val ev1: ￢[F[X] ∧ G[X]] = assumption.value
          val ev2: F[X] ∧ G[X] = forType[X].instantiate[F](forallF) ∧ forType[X].instantiate[G](forallG)
          ev2 ∧ ev1
        }
      }
      val impliedBy: ∀[[x <: Σ] => F[x] ∧ G[x]] => (∀[F] ∧ ∀[G]) = { forallFG =>
        val ev1: ∀[F] = byContradiction { notF => forType[notF.S].instantiate[[x <: Σ] => F[x] ∧ G[x]](forallFG)._1 ∧ notF.value }
        val ev2: ∀[G] = byContradiction { notF => forType[notF.S].instantiate[[x <: Σ] => F[x] ∧ G[x]](forallFG)._2 ∧ notF.value }
        ev1 ∧ ev2
      }
      implies ∧ impliedBy
    }

    def forallEquivCommute[F[_ <: Σ], G[_ <: Σ]]: ∀[[x <: Σ] => F[x] <=> G[x]] => ∀[[x <: Σ] => G[x] <=> F[x]] = { equiv =>
      byContradiction { assumption: ∃[[x <: Σ] => ￢[G[x] <=> F[x]]] =>
        type X = assumption.S
        val ev1: ￢[G[X] <=> F[X]] = assumption.value
        val ev2: F[X] <=> G[X] = forType[X].instantiate[[x <: Σ] => F[x] <=> G[x]](equiv)
        ev2.commute ∧ ev1
      }
    }

    def forallEquivTransitive[F[_ <: Σ], G[_ <: Σ], H[_ <: Σ]]
      : (∀[[x <: Σ] => F[x] <=> G[x]], ∀[[x <: Σ] => G[x] <=> H[x]]) => ∀[[x <: Σ] => F[x] <=> H[x]] = { case (fg, gh) =>
      byContradiction { assumption: ∃[[x <: Σ] => ￢[F[x] <=> H[x]]] =>
        type X = assumption.S
        val ev1: ￢[F[X] <=> H[X]] = assumption.value
        val ev2: F[X] <=> G[X] = forType[X].instantiate[[x <: Σ] => F[x] <=> G[x]](fg)
        val ev3: G[X] <=> H[X] = forType[X].instantiate[[x <: Σ] => G[x] <=> H[x]](gh)
        ev2.andThen(ev3) ∧ ev1
      }
    }

    def forallEquivConditions[F[_ <: Σ], G[_ <: Σ], H[_ <: Σ]](fg: ∀[[x <: Σ] => F[x] <=> G[x]], hg: ∀[[x <: Σ] => H[x] <=> G[x]]): ∀[[x <: Σ] => F[x] <=> H[x]] = {
      forallEquivTransitive[F, G, H](fg, forallEquivCommute[H, G](hg))
    }
  }

  /**
   * shorthand for axiom schema of separation.
   */
  def separate[X <: Σ, F[_ <: Σ]](implicit axiom: ZFSeparation): ∃[[y <: Σ] => ∀[[u <: Σ] => (u ∈ y) <=> ((u ∈ X) ∧ F[u])]] = {
    forType[X].instantiate[[x <: Σ] => ∃[[y <: Σ] => ∀[[u <: Σ] => (u ∈ y) <=> ((u ∈ x) ∧ F[u])]]](axiom.separation[F])
  }

  /**
   * If there exists a set containing all set u such that F[u], then there exists a subset containing all u such that F[u] and nothing else.
   */
  def comprehendsExactly[F[_ <: Σ]](existsSuperSet: ∃[[y <: Σ] => ∀[[z <: Σ] => F[z] => (z ∈ y)]])(implicit axiom: ZFSeparation): ∃[[y <: Σ] => ∀[[z <: Σ] => (z ∈ y) <=> F[z]]] = {
    type Y = existsSuperSet.S
    val ev1: ∀[[u <: Σ] => F[u] => (u ∈ Y)] = existsSuperSet.value
    val ev2: ∃[[w <: Σ] => ∀[[u <: Σ] => (u ∈ w) <=> ((u ∈ Y) ∧ F[u])]] = separate[Y, F]
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
  def setEquals[X <: Σ, Y <: Σ](containsSameElement: ∀[[z <: Σ] => (z ∈ X) <=> (z ∈ Y)])(implicit axiom: ZFExtensionality): X =::= Y = {
    forType2[X, Y].instantiate[[x <: Σ, y <: Σ] => ∀[[z <: Σ] => (z ∈ x) <=> (z ∈ y)] => (x =::= y)](axiom.extensionality)(containsSameElement)
  }

  /**
   * Two sets having the same equivalence condition on their elements are equal.
   */
  def equivalence[X <: Σ, Y <: Σ, F[_ <: Σ]](implicit axiom: ZFExtensionality): (∀[[w <: Σ] => (w ∈ X) <=> F[w]] ∧ ∀[[w <: Σ] => (w ∈ Y) <=> F[w]]) => (X =::= Y) = { case (x, y) =>
    val ev1: ∀[[x <: Σ] => x ∈ X <=> x ∈ Y] = Predicate.forallEquivConditions[[w <: Σ] => w ∈ X, F, [w <: Σ] => w ∈ Y](x, y)
    setEquals[X, Y](ev1)
  }

  def uniqueExistence[R[_ <: Σ, _ <: Σ]](exists: ∀[[x <: Σ] => ∃[[y <: Σ] => R[y, x]]],
                                         unique: ∀[[x <: Σ] => Unique[[y <: Σ] => R[y, x]]]): ∀[[x <: Σ] => ∃![[y <: Σ] => R[y, x]]] = {
    Predicate.forallConj[[x <: Σ] => ∃[[y <: Σ] => R[y, x]], [x <: Σ] => Unique[[y <: Σ] => R[y, x]]].implies(exists ∧ unique)
  }

  def uniqueExistence2[R[_ <: Σ, _ <: Σ, _ <: Σ]](exists: ∀[[x <: Σ] => ∀[[y <: Σ] => ∃[[z <: Σ] => R[z, x, y]]]],
                                                  unique: ∀[[x <: Σ] => ∀[[y <: Σ] => Unique[[z <: Σ] => R[z, x, y]]]])
    : ∀[[x <: Σ] => ∀[[y <: Σ] => ∃![[z <: Σ] => R[z, x, y]]]] = {
      byContradiction { assumption: ∃[[x <: Σ] => ￢[∀[[y <: Σ] => ∃![[z <: Σ] => R[z, x, y]]]]] =>
        type X = assumption.S
        type RX[z <: Σ, y <: Σ] = R[z, X, y]
        val ev1: ￢[∀[[y <: Σ] => ∃![[z <: Σ] => RX[z, y]]]] = assumption.value
        val ev2: ∀[[y <: Σ] => ∃[[z <: Σ] => RX[z, y]]] = forType[X].instantiate[[x <: Σ] => ∀[[y <: Σ] => ∃[[z <: Σ] => R[z, x, y]]]](exists)
        val ev3: ∀[[y <: Σ] => Unique[[z <: Σ] => RX[z, y]]] = forType[X].instantiate[[x <: Σ] => ∀[[y <: Σ] => Unique[[z <: Σ] => R[z, x, y]]]](unique)
        uniqueExistence[RX](ev2, ev3) ∧ ev1
      }
  }

  /**
   * creates a class function(_ <: Σ => Σ) given the that the relation forms a function on types.
   */
  def createUnaryClassFunction[R[_ <: Σ, _ <: Σ]](uniqueExists: ∀[[x <: Σ] => ∃![[y <: Σ] => y R x]])
    : ∃~>[[ClassFunction[_ <: Σ] <: Σ] => ∀[[x <: Σ] => ClassFunction[x] R x]] = {
    new ∃~>[[ClassFunction[_ <: Σ] <: Σ] => ∀[[x <: Σ] => ClassFunction[x] R x]] {
      type F[x <: Σ] = ∃[[y <: Σ] => y R x]#S
      val value: ∀[[x <: Σ] => F[x] R x] = {
        byContradiction { assumption: ∃[[x <: Σ] => ￢[F[x] R x]] =>
          type X = assumption.S
          type RX[y <: Σ] = y R X
          val ev1: ￢[RX[F[X]]] = assumption.value
          val ev2: ∃![RX] = forType[X].instantiate[[x <: Σ] => ∃![[y <: Σ] => y R x]](uniqueExists)
          type Y = ev2._1.S
          val ev3: RX[Y] = ev2._1.value
          val ev4: RX[F[X]] = Isomorphisms.uniqueness(ev2, ev3).sub[RX](ev3)
          ev4 ∧ ev1
        }
      }
    }
  }

  /**
   * creates a class function(_ <: Σ, _ <: Σ => Σ) given the that the relation forms a function on types.
   */
  def createBinaryClassFunction[R[_ <: Σ, _ <: Σ, _ <: Σ]](uniqueExists: ∀[[x <: Σ] => ∀[[y <: Σ] => ∃![[z <: Σ] => R[z, x, y]]]])
    : ∃~~>[[ClassFunction[_ <: Σ, _ <: Σ] <: Σ] => ∀[[x <: Σ] => ∀[[y <: Σ] => R[ClassFunction[x, y], x, y]]]] = {
      new ∃~~>[[ClassFunction[_ <: Σ, _ <: Σ] <: Σ] => ∀[[x <: Σ] => ∀[[y <: Σ] => R[ClassFunction[x, y], x, y]]]] {
        type F[x <: Σ, y <: Σ] = ∃[[z <: Σ] => R[z, x, y]]#S
        val value: ∀[[x <: Σ] => ∀[[y <: Σ] => R[F[x, y], x, y]]] = {
          byContradiction { assumption: ∃[[x <: Σ] => ￢[∀[[y <: Σ] => R[F[x, y], x, y]]]] =>
            type X = assumption.S
            val ev1: ∃[[y <: Σ] => ￢[R[F[X, y], X, y]]] = assumption.value
            type Y = ev1.S
            type RXY[z <: Σ] = R[z, X, Y]
            val ev2: ￢[RXY[F[X, Y]]] = ev1.value
            val ev3: ∃![RXY] = forType2[X, Y].instantiate[[x <: Σ, y <: Σ] => ∃![[z <: Σ] => R[z, x, y]]](uniqueExists)
            type Z = ev3._1.S
            val ev4: RXY[Z] = ev3._1.value
            val ev5: RXY[F[X, Y]] = Isomorphisms.uniqueness(ev3, ev4).sub[RXY](ev4)

            ev5 ∧ ev2
          }
        }
      }
  }
  
}
