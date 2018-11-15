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
import com.github.kory33.proof.set.logic.SetDomain
import com.github.kory33.proof.logic.predicate.Equality._
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set._

object Lemma {

  object Predicate {
    def forallConj[F[_], G[_]]: (∀[F] ∧ ∀[G]) <=> ∀[[x] => F[x] ∧ G[x]] = {
      val implies: (∀[F] ∧ ∀[G]) => ∀[[x] => F[x] ∧ G[x]] = { case (forallF, forallG) =>
        byContradiction { implicit assumption: ∃[[x] => ￢[F[x] ∧ G[x]]] =>
          type X = assumption.S
          val ev1: ￢[F[X] ∧ G[X]] = assumption.instance
          val ev2: F[X] ∧ G[X] = forType[X].instantiate[F](forallF) ∧ forType[X].instantiate[G](forallG)
          ev2 ∧ ev1
        }
      }
      val impliedBy: ∀[[x] => F[x] ∧ G[x]] => (∀[F] ∧ ∀[G]) = { forallFG =>
        val ev1: ∀[F] = byContradiction { implicit notF => forType[notF.S].instantiate[[x] => F[x] ∧ G[x]](forallFG)._1 ∧ notF.instance }
        val ev2: ∀[G] = byContradiction { implicit notF => forType[notF.S].instantiate[[x] => F[x] ∧ G[x]](forallFG)._2 ∧ notF.instance }
        ev1 ∧ ev2
      }
      implies ∧ impliedBy
    }

    def forallEquivCommute[F[_], G[_]]: ∀[[x] => F[x] <=> G[x]] => ∀[[x] => G[x] <=> F[x]] = { equiv =>
      byContradiction { implicit assumption: ∃[[x] => ￢[G[x] <=> F[x]]] =>
        type X = assumption.S
        val ev1: ￢[G[X] <=> F[X]] = assumption.instance
        val ev2: F[X] <=> G[X] = forType[X].instantiate[[x] => F[x] <=> G[x]](equiv)
        ev2.commute ∧ ev1
      }
    }

    def forallEquivTransitive[F[_], G[_], H[_]]
      : (∀[[x] => F[x] <=> G[x]], ∀[[x] => G[x] <=> H[x]]) => ∀[[x] => F[x] <=> H[x]] = { case (fg, gh) =>
      byContradiction { implicit assumption: ∃[[x] => ￢[F[x] <=> H[x]]] =>
        type X = assumption.S
        val ev1: ￢[F[X] <=> H[X]] = assumption.instance
        val ev2: F[X] <=> G[X] = forType[X].instantiate[[x] => F[x] <=> G[x]](fg)
        val ev3: G[X] <=> H[X] = forType[X].instantiate[[x] => G[x] <=> H[x]](gh)
        ev2.andThen(ev3) ∧ ev1
      }
    }

    def forallEquivConditions[F[_], G[_], H[_]](fg: ∀[[x] => F[x] <=> G[x]], hg: ∀[[x] => H[x] <=> G[x]]): ∀[[x] => F[x] <=> H[x]] = {
      forallEquivTransitive[F, G, H](fg, forallEquivCommute[H, G](hg))
    }
  }

  /**
   * shorthand for axiom schema of separation.
   */
  def separate[X : SetDomain, F[_]](implicit axiom: ZFSeparation): ∃[[y] => ∀[[u] => (u ∈ y) <=> ((u ∈ X) ∧ F[u])]] = {
    forType[X].instantiate[[x] => ∃[[y] => ∀[[u] => (u ∈ y) <=> ((u ∈ x) ∧ F[u])]]](axiom.separation[F])
  }

  /**
   * If there exists a set containing all set u such that F[u], then there exists a subset containing all u such that F[u] and nothing else.
   */
  def comprehendsExactly[F[_]](existsSuperSet: ∃[[y] => ∀[[z] => F[z] => (z ∈ y)]])(implicit axiom: ZFSeparation): ∃[[y] => ∀[[z] => (z ∈ y) <=> F[z]]] = {
    implicit val implicitExists = existsSuperSet
    type Y = implicitExists.S
    val ev1: ∀[[u] => F[u] => (u ∈ Y)] = implicitExists.instance
    implicit val ev2: ∃[[w] => ∀[[u] => (u ∈ w) <=> ((u ∈ Y) ∧ F[u])]] = separate[Y, F]
    type W = ev2.S
    val ev3: ∀[[u] => (u ∈ W) <=> ((u ∈ Y) ∧ F[u])] = ev2.instance
    val ev4: ∀[[u] => (u ∈ W) <=> F[u]] = byContradiction { implicit assumption: ∃[[u] => ￢[(u ∈ W) <=> F[u]]] =>
      type U = assumption.S
      val ev41: ￢[(U ∈ W) <=> F[U]] = assumption.instance
      val ev42: (U ∈ W) <=> ((U ∈ Y) ∧ F[U]) = forType[U].instantiate[[u] => (u ∈ W) <=> ((u ∈ Y) ∧ F[u])](ev3)
      val ev43: (U ∈ W) => F[U] = ev42.implies.andThen(_._2)
      val ev44: F[U] => (U ∈ Y) = forType[U].instantiate[[u] => F[u] => (u ∈ Y)](ev1)
      val ev45: F[U] => (U ∈ W) = { fu: F[U] => ev42.impliedBy(ev44(fu) ∧ fu) }
      val ev46: (U ∈ W) <=> F[U] = ev43 ∧ ev45
      ev46 ∧ ev41
    }
    forType[W].generalize[[y] => ∀[[z] => (z ∈ y) <=> F[z]]](ev4)
  }

  /**
   * shorthand for axiom of extensionality.
   */
  def setEquals[X : SetDomain, Y : SetDomain](containsSameElement: ∀[[z] => (z ∈ X) <=> (z ∈ Y)])(implicit axiom: ZFExtensionality): X =::= Y = {
    forType2[X, Y].instantiate[[x, y] => ∀[[z] => (z ∈ x) <=> (z ∈ y)] => (x =::= y)](axiom.extensionality)(containsSameElement)
  }

  /**
   * Two sets having the same equivalence condition on their elements are equal.
   */
  def equivalence[X : SetDomain, Y : SetDomain, F[_]](implicit axiom: ZFExtensionality): (∀[[w] => (w ∈ X) <=> F[w]] ∧ ∀[[w] => (w ∈ Y) <=> F[w]]) => (X =::= Y) = { case (x, y) =>
    val ev1: ∀[[x] => x ∈ X <=> x ∈ Y] = Predicate.forallEquivConditions[[w] => w ∈ X, F, [w] => w ∈ Y](x, y)
    setEquals[X, Y](ev1)
  }

  def uniqueExistence[R[_, _]](exists: ∀[[x] => ∃[[y] => R[y, x]]],
                                         unique: ∀[[x] => Unique[[y] => R[y, x]]]): ∀[[x] => ∃![[y] => R[y, x]]] = {
    Predicate.forallConj[[x] => ∃[[y] => R[y, x]], [x] => Unique[[y] => R[y, x]]].implies(exists ∧ unique)
  }

  def uniqueExistence2[R[_, _, _]](exists: ∀[[x] => ∀[[y] => ∃[[z] => R[z, x, y]]]],
                                                  unique: ∀[[x] => ∀[[y] => Unique[[z] => R[z, x, y]]]])
    : ∀[[x] => ∀[[y] => ∃![[z] => R[z, x, y]]]] = {
      byContradiction { implicit assumption: ∃[[x] => ￢[∀[[y] => ∃![[z] => R[z, x, y]]]]] =>
        type X = assumption.S
        type RX[z, y] = R[z, X, y]
        val ev1: ￢[∀[[y] => ∃![[z] => RX[z, y]]]] = assumption.instance
        val ev2: ∀[[y] => ∃[[z] => RX[z, y]]] = forType[X].instantiate[[x] => ∀[[y] => ∃[[z] => R[z, x, y]]]](exists)
        val ev3: ∀[[y] => Unique[[z] => RX[z, y]]] = forType[X].instantiate[[x] => ∀[[y] => Unique[[z] => R[z, x, y]]]](unique)
        uniqueExistence[RX](ev2, ev3) ∧ ev1
      }
  }

  /**
   * creates a class function(_ => Σ) given the that the relation forms a function on types.
   */
  def createUnaryClassFunction[R[_, _]](uniqueExists: ∀[[x] => ∃![[y] => y R x]])
    : ∃~>[[ClassFunction[_]] => ∀[[x] => ClassFunction[x] R x]] = {
    new ∃~>[[ClassFunction[_]] => ∀[[x] => ClassFunction[x] R x]] {
      type F[x] = ∃[[y] => y R x]#S

      val instance: ∀[[x] => F[x] R x] = {
        byContradiction { implicit assumption: ∃[[x] => ￢[F[x] R x]] =>
          type X = assumption.S
          type RX[y] = y R X
          val ev1: ￢[RX[F[X]]] = assumption.instance
          val ev2: ∃![RX] = forType[X].instantiate[[x] => ∃![[y] => y R x]](uniqueExists)
          implicit val existsY = ev2._1
          type Y = existsY.S
          val ev3: RX[Y] = existsY.instance
          val ev4: RX[F[X]] = Isomorphisms.uniqueness(ev2, ev3).sub[RX](ev3)
          ev4 ∧ ev1
        }
      }

      def typeclass[X : SetDomain]: SetDomain[F[X]] = {
          type RX[y] = y R X
          val ev1: ∃![RX] = forType[X].instantiate[[x] => ∃![[y] => y R x]](uniqueExists)
          implicit val existsY = ev1._1
          type Y = existsY.S
          val ev2: RX[Y] = existsY.instance
          val ev3: SetDomain[Y] = existsY.typeclass
          val ev4: Y =::= F[X] = Isomorphisms.uniqueness(ev1, ev2)
          ev4.sub[SetDomain](ev3)
      }
    }
  }

  /**
   * creates a class function(_, _ => Σ) given the that the relation forms a function on types.
   */
  def createBinaryClassFunction[R[_, _, _]](uniqueExists: ∀[[x] => ∀[[y] => ∃![[z] => R[z, x, y]]]])
    : ∃~~>[[ClassFunction[_, _]] => ∀[[x] => ∀[[y] => R[ClassFunction[x, y], x, y]]]] = {
      new ∃~~>[[ClassFunction[_, _]] => ∀[[x] => ∀[[y] => R[ClassFunction[x, y], x, y]]]] {
        type F[x, y] = ∃[[z] => R[z, x, y]]#S

        val instance: ∀[[x] => ∀[[y] => R[F[x, y], x, y]]] = {
          byContradiction { implicit assumption: ∃[[x] => ￢[∀[[y] => R[F[x, y], x, y]]]] =>
            type X = assumption.S
            implicit val ev1: ∃[[y] => ￢[R[F[X, y], X, y]]] = assumption.instance
            type Y = ev1.S
            type RXY[z] = R[z, X, Y]
            val ev2: ￢[RXY[F[X, Y]]] = ev1.instance
            val ev3: ∃![RXY] = forType2[X, Y].instantiate[[x, y] => ∃![[z] => R[z, x, y]]](uniqueExists)
            implicit val implicitZ = ev3._1
            type Z = implicitZ.S
            val ev4: RXY[Z] = implicitZ.instance
            val ev5: RXY[F[X, Y]] = Isomorphisms.uniqueness(ev3, ev4).sub[RXY](ev4)

            ev5 ∧ ev2
          }
        }

        def typeclass[X : SetDomain, Y : SetDomain]: SetDomain[F[X, Y]] = {
          type RXY[z] = R[z, X, Y]
          val ev1: ∃![RXY] = forType2[X, Y].instantiate[[x, y] => ∃![[z] => R[z, x, y]]](uniqueExists)
          implicit val existsY = ev1._1
          type Z = existsY.S
          val ev2: RXY[Z] = existsY.instance
          val ev3: SetDomain[Z] = existsY.typeclass
          val ev4: Z =::= F[X, Y] = Isomorphisms.uniqueness(ev1, ev2)
          ev4.sub[SetDomain](ev3)
        }
      }
  }  
}
