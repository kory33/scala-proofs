package com.github.kory33.proof.set.zf.operators

import scala.language.implicitConversions

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.logic.propositional.ClassicalLogicSystem._
import com.github.kory33.proof.set.axiom.zf._
import com.github.kory33.proof.set.logic.SetDomain
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateSystem._
import com.github.kory33.proof.logic.predicate.Equality._
import com.github.kory33.proof.set.zf.Lemma._
import com.github.kory33.proof.set.zf.Lemma.Predicate._
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set._

class UnionSetConstruct(implicit axiom: ZFSeparation & ZFExtensionality & ZFUnion) {

  val existence: ∀[[x] => ∃[[y] => y isUnionOf x]] = {
    byContradiction { implicit assumption: ∃[[x] => ￢[∃[[y] => y isUnionOf x]]] =>
      type F = assumption.S
      val ev1: ￢[∃[[u] => u isUnionOf F]] = assumption.instance
      implicit val ev2: ∃[[u] => ∀[[y] => ∀[[x] => ((x ∈ y) ∧ (y ∈ F)) => x ∈ u]]] = {
        forType[F].instantiate[[F] => ∃[[u] => ∀[[y] => ∀[[x] => ((x ∈ y) ∧ (y ∈ F)) => x ∈ u]]]](axiom.union)
      }
      type U = ev2.S
      val ev3: ∀[[y] => ∀[[x] => ((x ∈ y) ∧ (y ∈ F)) => x ∈ U]] = ev2.instance
      val ev4: ∃[[u] => ∀[[x] => (x ∈ u) <=> ∃[[Y] => ((x ∈ Y) ∧ (Y ∈ F))]]] = {
        implicit val ev41: ∃[[v] => ∀[[x] => (x ∈ v) <=> (x ∈ U) ∧ ∃[[y] => ((x ∈ y) ∧ (y ∈ F))]]] = {
          separate[U, [x] => ∃[[y] => ((x ∈ y) ∧ (y ∈ F))]]
        }
        type V = ev41.S
        val ev42: ∀[[x] => (x ∈ V) <=> ((x ∈ U) ∧ ∃[[y] => ((x ∈ y) ∧ (y ∈ F))])] = ev41.instance
        val ev43: ∀[[x] => (x ∈ V) <=> ∃[[Y] => ((x ∈ Y) ∧ (Y ∈ F))]] = {
          val ev431: ∀[[x] => ((x ∈ U) ∧ ∃[[y] => ((x ∈ y) ∧ (y ∈ F))]) <=> ∃[[Y] => ((x ∈ Y) ∧ (Y ∈ F))]] = byContradiction { implicit assumption431 =>
            type X = assumption431.S
            val ev4311: ￢[((X ∈ U) ∧ ∃[[y] => ((X ∈ y) ∧ (y ∈ F))]) <=> ∃[[Y] => ((X ∈ Y) ∧ (Y ∈ F))]] = assumption431.instance
            val implies: ((X ∈ U) ∧ ∃[[y] => ((X ∈ y) ∧ (y ∈ F))]) => ∃[[Y] => ((X ∈ Y) ∧ (Y ∈ F))] = { _._2 }
            val impliedBy: ∃[[Y] => ((X ∈ Y) ∧ (Y ∈ F))] => ((X ∈ U) ∧ ∃[[y] => ((X ∈ y) ∧ (y ∈ F))]) = { implicit ex =>
              type Y = ex.S
              val ev4321: (X ∈ Y) ∧ (Y ∈ F) = ex.instance
              val ev4322: ((X ∈ Y) ∧ (Y ∈ F)) => X ∈ U = forType2[Y, X].instantiate[[y, x] => ((x ∈ y) ∧ (y ∈ F)) => x ∈ U](ev3)
              val ev4323: X ∈ U = ev4322(ev4321)
              ev4323 ∧ ex
            }
            val ev4312: ((X ∈ U) ∧ ∃[[y] => ((X ∈ y) ∧ (y ∈ F))]) <=> ∃[[Y] => ((X ∈ Y) ∧ (Y ∈ F))] = implies ∧ impliedBy
            ev4312 ∧ ev4311
          }
          forallEquivTransitive[[x] => x ∈ V, [x] => (x ∈ U) ∧ ∃[[y] => ((x ∈ y) ∧ (y ∈ F))], [x] => ∃[[Y] => ((x ∈ Y) ∧ (Y ∈ F))]](ev42, ev431)
        }
        genExist[[u] => ∀[[x] => (x ∈ u) <=> ∃[[Y] => ((x ∈ Y) ∧ (Y ∈ F))]], V](ev43)
      }
      val ev5: ∃[[u] => u isUnionOf F] = ev4
      ev5 ∧ ev1
    }
  }

  val uniqueness: ∀[[x] => Unique[[y] => y isUnionOf x]] = {
    byContradiction { assumption: ￢[∀[[z] => ∀[[x] => ∀[[y] => (x isUnionOf z) ∧ (y isUnionOf z) => x =::= y]]]] =>
      implicit val ev1: ∃[[z] => ∃[[x] => ∃[[y] => ￢[(x isUnionOf z) ∧ (y isUnionOf z) => x =::= y]]]] = {
        notForall3[[z, x, y] => (x isUnionOf z) ∧ (y isUnionOf z) => x =::= y](assumption)
      }
      type Z = ev1.S
      implicit val ev11 = ev1.instance
      type X = ev11.S
      implicit val ev12 = ev11.instance
      type Y = ev12.S
      val ev2: ￢[(X isUnionOf Z) ∧ (Y isUnionOf Z) => X =::= Y] = ev12.instance
      val ev3: (X isUnionOf Z) ∧ (Y isUnionOf Z) => X =::= Y = equivalence[X, Y, [x] => ∃[[Y] => ((x ∈ Y) ∧ (Y ∈ Z))]]
      ev3 ∧ ev2
    }
  }

  val unionFunctionExistence: ∃~>[[Union[_]] => ∀[[x] => Union[x] isUnionOf x]] = {
    createUnaryClassFunction[isUnionOf](uniqueExistence[isUnionOf](existence, uniqueness))
  }

  type Union[x] = unionFunctionExistence.F[x]

  val constraintValue: ∀[[x] => Union[x] isUnionOf x] = unionFunctionExistence.instance

  implicit def familyUnionIsSet[x : SetDomain]: SetDomain[Union[x]] = unionFunctionExistence.typeclass[x]

  def constraint[x : SetDomain]: Union[x] isUnionOf x = forType[x].instantiate[[x] => Union[x] isUnionOf x](constraintValue)
  def constraint2[F : SetDomain, x : SetDomain]: (x ∈ Union[F]) <=> ∃[[Y] => ((x ∈ Y) ∧ (Y ∈ F))] = {
    forType[x].instantiate[[z] => (z ∈ Union[F]) <=> ∃[[Y] => ((z ∈ Y) ∧ (Y ∈ F))]](constraint[F])
  }
}

class BinaryUnionConstruct(val pairSet: PairSetConstruct, val unionSet: UnionSetConstruct)(implicit axiom: ZFExtensionality) {

  type Union = unionSet.Union
  type ++: = pairSet.++:

  type ∪[x, y] = Union[x ++: y]
  
  val constraintValue: ∀[[x] => ∀[[y] => isSumOf[x ∪ y, x, y]]] = {
    import pairSet.pairIsSet

    byContradiction { assumption: ￢[∀[[x] => ∀[[y] => isSumOf[x ∪ y, x, y]]]] =>
      implicit val ev1 = notForall2[[x, y] => isSumOf[x ∪ y, x, y]](assumption)
      type X = ev1.S
      implicit val ev11 = ev1.instance
      type Y = ev11.S
      val ev2: ￢[isSumOf[X ∪ Y, X, Y]] = ev11.instance
      val ev3: isSumOf[X ∪ Y, X, Y] = byContradiction { implicit assumption3: ∃[[w] => ￢[(w ∈ (X ∪ Y)) <=> ((w ∈ X) ∨ (w ∈ Y))]] =>
        type W = assumption3.S
        val ev31: ￢[(W ∈ (X ∪ Y)) <=> ((W ∈ X) ∨ (W ∈ Y))] = assumption3.instance
        val ev32: (W ∈ (X ∪ Y)) => ((W ∈ X) ∨ (W ∈ Y)) = { assumption32 =>
          implicit val ev321: ∃[[z] => ((W ∈ z) ∧ (z ∈ (X ++: Y)))] = unionSet.constraint2[X ++: Y, W].implies(assumption32)
          type Z = ev321.S
          val ev322: W ∈ Z = ev321.instance._1
          val ev323: Z ∈ (X ++: Y) = ev321.instance._2
          val ev324: (Z =::= X) ∨ (Z =::= Y) = pairSet.constraint2[Z, X, Y].implies(ev323)
          ev324 match {
            case Left(zEqX) => Left(zEqX.sub(ev322))
            case Right(zEqY) => Right(zEqY.sub(ev322))
          }
        }
        val ev33: ((W ∈ X) ∨ (W ∈ Y)) => (W ∈ (X ∪ Y)) = { assumption33 =>
          val ev331: ∃[[z] => ((W ∈ z) ∧ (z ∈ (X ++: Y)))] = assumption33 match {
            case Left(wInX) => forType[X].generalize(wInX ∧ pairSet.containsLeft[X, Y])
            case Right(wInY) => forType[Y].generalize(wInY ∧ pairSet.containsRight[X, Y])
          }
          unionSet.constraint2[X ++: Y, W].impliedBy(ev331)
        }
        val ev34: (W ∈ (X ∪ Y)) <=> ((W ∈ X) ∨ (W ∈ Y)) = ev32 ∧ ev33
        ev34 ∧ ev31
      }
      ev3 ∧ ev2
    }
  }

  implicit def binaryUnionIsSet[X: SetDomain, Y: SetDomain]: SetDomain[X ∪ Y] = unionSet.familyUnionIsSet(pairSet.pairIsSet)

  def constraint[x : SetDomain, y : SetDomain]: isSumOf[x ∪ y, x, y] = forType2[x, y].instantiate[[x1, y1] => isSumOf[x1 ∪ y1, x1, y1]](constraintValue)

  def constraint2[x : SetDomain, X : SetDomain, Y : SetDomain]: (x ∈ (X ∪ Y)) <=> ((x ∈ X) ∨ (x ∈ Y)) = {
    forType[x].instantiate[[w] => (w ∈ (X ∪ Y)) <=> (w ∈ X) ∨ (w ∈ Y)](constraint[X, Y])
  }

  def commute[X : SetDomain, Y : SetDomain]: (X ∪ Y) =::= (Y ∪ X) = {
    val ev1: ∀[[x] => (x ∈ (X ∪ Y)) <=> (x ∈ (Y ∪ X))] = byContradiction { implicit assumption: ∃[[x] => ￢[(x ∈ (X ∪ Y)) <=> (x ∈ (Y ∪ X))]] =>
      type X1 = assumption.S
      val ev11: ￢[(X1 ∈ (X ∪ Y)) <=> (X1 ∈ (Y ∪ X))] = assumption.instance
      val ev12: (X1 ∈ (X ∪ Y)) => (X1 ∈ (Y ∪ X)) = { x1InXY =>
        constraint2[X1, Y, X].impliedBy(constraint2[X1, X, Y].implies(x1InXY).commute)
      }
      val ev13: (X1 ∈ (Y ∪ X)) => (X1 ∈ (X ∪ Y)) = { x1InYX =>
        constraint2[X1, X, Y].impliedBy(constraint2[X1, Y, X].implies(x1InYX).commute)
      }
      val ev14: (X1 ∈ (X ∪ Y)) <=> (X1 ∈ (Y ∪ X)) = ev12 ∧ ev13
      ev14 ∧ ev11
    }

    setEquals[X ∪ Y, Y ∪ X](ev1)
  }

  def includesLeft[X : SetDomain, Y : SetDomain]: X ⊂ (X ∪ Y) = byContradiction { implicit assumption: ∃[[x] => ￢[(x ∈ X) => (x ∈ (X ∪ Y))]] =>
    type X1 = assumption.S
    val ev1: ￢[(X1 ∈ X) => (X1 ∈ (X ∪ Y))] = assumption.instance
    val ev2: (X1 ∈ X) => (X1 ∈ (X ∪ Y)) = { x1InX => constraint2[X1, X, Y].impliedBy(Left(x1InX)) }
    ev2 ∧ ev1
  }

  def includesRight[X : SetDomain, Y : SetDomain]: Y ⊂ (X ∪ Y) = commute[Y, X].sub(includesLeft[Y, X])

  def containsLeft[x : SetDomain, X : SetDomain, Y : SetDomain](xInX: x ∈ X): (x ∈ (X ∪ Y)) = {
    forType[x].instantiate[[x1] => (x1 ∈ X) => (x1 ∈ (X ∪ Y))](includesLeft[X, Y])(xInX)
  }

  def containsRight[y : SetDomain, X : SetDomain, Y : SetDomain](yInY: y ∈ Y): (y ∈ (X ∪ Y)) = {
    commute[Y, X].sub[[xy] => (y ∈ Y) => (y ∈ xy)](containsLeft[y, Y, X])(yInY)
  }

}
