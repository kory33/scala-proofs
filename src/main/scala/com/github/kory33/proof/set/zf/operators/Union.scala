package com.github.kory33.proof.set.zf.operators

import scala.language.implicitConversions

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.logic.propositional.ClassicalLogicSystem._
import com.github.kory33.proof.set.axiom.zf._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateSystem._
import com.github.kory33.proof.set.logic.Equality._
import com.github.kory33.proof.set.zf.Lemma._
import com.github.kory33.proof.set.zf.Lemma.Predicate._
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set._

class UnionSetConstruct(implicit axiom: ZFSeparation & ZFExtensionality & ZFUnion) {

  val existence: ∀[[x <: Σ] => ∃[[y <: Σ] => y isUnionOf x]] = {
    byContradiction { assumption: ∃[[x <: Σ] => ￢[∃[[y <: Σ] => y isUnionOf x]]] =>
      type F = assumption.S 
      val ev1: ￢[∃[[u <: Σ] => u isUnionOf F]] = assumption.value
      val ev2: ∃[[u <: Σ] => ∀[[y <: Σ] => ∀[[x <: Σ] => ((x ∈ y) ∧ (y ∈ F)) => x ∈ u]]] = {
        forType[F].instantiate[[F <: Σ] => ∃[[u <: Σ] => ∀[[y <: Σ] => ∀[[x <: Σ] => ((x ∈ y) ∧ (y ∈ F)) => x ∈ u]]]](axiom.union)
      }
      type U = ev2.S
      val ev3: ∀[[y <: Σ] => ∀[[x <: Σ] => ((x ∈ y) ∧ (y ∈ F)) => x ∈ U]] = ev2.value
      val ev4: ∃[[u <: Σ] => ∀[[x <: Σ] => (x ∈ u) <=> ∃[[Y <: Σ] => ((x ∈ Y) ∧ (Y ∈ F))]]] = {
        val ev41: ∃[[v <: Σ] => ∀[[x <: Σ] => (x ∈ v) <=> (x ∈ U) ∧ ∃[[y <: Σ] => ((x ∈ y) ∧ (y ∈ F))]]] = {
          separate[U, [x <: Σ] => ∃[[y <: Σ] => ((x ∈ y) ∧ (y ∈ F))]]
        }
        type V = ev41.S
        val ev42: ∀[[x <: Σ] => (x ∈ V) <=> ((x ∈ U) ∧ ∃[[y <: Σ] => ((x ∈ y) ∧ (y ∈ F))])] = ev41.value
        val ev43: ∀[[x <: Σ] => (x ∈ V) <=> ∃[[Y <: Σ] => ((x ∈ Y) ∧ (Y ∈ F))]] = {
          val ev431: ∀[[x <: Σ] => ((x ∈ U) ∧ ∃[[y <: Σ] => ((x ∈ y) ∧ (y ∈ F))]) <=> ∃[[Y <: Σ] => ((x ∈ Y) ∧ (Y ∈ F))]] = byContradiction { assumption431 =>
            type X = assumption431.S
            val ev4311: ￢[((X ∈ U) ∧ ∃[[y <: Σ] => ((X ∈ y) ∧ (y ∈ F))]) <=> ∃[[Y <: Σ] => ((X ∈ Y) ∧ (Y ∈ F))]] = assumption431.value
            val implies: ((X ∈ U) ∧ ∃[[y <: Σ] => ((X ∈ y) ∧ (y ∈ F))]) => ∃[[Y <: Σ] => ((X ∈ Y) ∧ (Y ∈ F))] = { _._2 }
            val impliedBy: ∃[[Y <: Σ] => ((X ∈ Y) ∧ (Y ∈ F))] => ((X ∈ U) ∧ ∃[[y <: Σ] => ((X ∈ y) ∧ (y ∈ F))]) = { ex =>
              type Y = ex.S
              val ev4321: (X ∈ Y) ∧ (Y ∈ F) = ex.value
              val ev4322: ((X ∈ Y) ∧ (Y ∈ F)) => X ∈ U = forType2[Y, X].instantiate[[y <: Σ, x <: Σ] => ((x ∈ y) ∧ (y ∈ F)) => x ∈ U](ev3)
              val ev4323: X ∈ U = ev4322(ev4321)
              ev4323 ∧ ex
            }
            val ev4312: ((X ∈ U) ∧ ∃[[y <: Σ] => ((X ∈ y) ∧ (y ∈ F))]) <=> ∃[[Y <: Σ] => ((X ∈ Y) ∧ (Y ∈ F))] = implies ∧ impliedBy
            ev4312 ∧ ev4311
          }
          forallEquivTransitive[[x <: Σ] => x ∈ V, [x <: Σ] => (x ∈ U) ∧ ∃[[y <: Σ] => ((x ∈ y) ∧ (y ∈ F))], [x <: Σ] => ∃[[Y <: Σ] => ((x ∈ Y) ∧ (Y ∈ F))]](ev42, ev431)
        }
        genExist[[u <: Σ] => ∀[[x <: Σ] => (x ∈ u) <=> ∃[[Y <: Σ] => ((x ∈ Y) ∧ (Y ∈ F))]], V](ev43)
      }
      val ev5: ∃[[u <: Σ] => u isUnionOf F] = ev4
      ev5 ∧ ev1
    }
  }

  val uniqueness: ∀[[x <: Σ] => Unique[[y <: Σ] => y isUnionOf x]] = {
    byContradiction { assumption: ￢[∀[[z <: Σ] => ∀[[x <: Σ] => ∀[[y <: Σ] => (x isUnionOf z) ∧ (y isUnionOf z) => x =::= y]]]] =>
      val ev1: ∃[[z <: Σ] => ∃[[x <: Σ] => ∃[[y <: Σ] => ￢[(x isUnionOf z) ∧ (y isUnionOf z) => x =::= y]]]] = {
        notForall3[[z <: Σ, x <: Σ, y <: Σ] => (x isUnionOf z) ∧ (y isUnionOf z) => x =::= y](assumption)
      }
      type Z = ev1.S; type X = ev1.value.S; type Y = ev1.value.value.S
      val ev2: ￢[(X isUnionOf Z) ∧ (Y isUnionOf Z) => X =::= Y] = ev1.value.value.value
      val ev3: (X isUnionOf Z) ∧ (Y isUnionOf Z) => X =::= Y = equivalence[X, Y, [x <: Σ] => ∃[[Y <: Σ] => ((x ∈ Y) ∧ (Y ∈ Z))]]
      ev3 ∧ ev2
    }
  }

  val unionFunctionExistence: ∃~>[[Union[_ <: Σ] <: Σ] => ∀[[x <: Σ] => Union[x] isUnionOf x]] = {
    createUnaryClassFunction[isUnionOf](uniqueExistence[isUnionOf](existence, uniqueness))
  }

  type Union[x <: Σ] = unionFunctionExistence.F[x]
  val constraintValue: ∀[[x <: Σ] => Union[x] isUnionOf x] = unionFunctionExistence.value
  def constraint[x <: Σ]: Union[x] isUnionOf x = forType[x].instantiate[[x <: Σ] => Union[x] isUnionOf x](constraintValue)
  def constraint2[F <: Σ, x <: Σ]: (x ∈ Union[F]) <=> ∃[[Y <: Σ] => ((x ∈ Y) ∧ (Y ∈ F))] = {
    forType[x].instantiate[[z <: Σ] => (z ∈ Union[F]) <=> ∃[[Y <: Σ] => ((z ∈ Y) ∧ (Y ∈ F))]](constraint[F])
  }
}

class BinaryUnionConstruct(val pairSet: PairSetConstruct, val unionSet: UnionSetConstruct)(implicit axiom: ZFExtensionality) {

  type Union = unionSet.Union
  type ++: = pairSet.++:

  type ∪[x <: Σ, y <: Σ] = Union[x ++: y]
  
  val constraintValue: ∀[[x <: Σ] => ∀[[y <: Σ] => isSumOf[x ∪ y, x, y]]] = {
    byContradiction { assumption: ￢[∀[[x <: Σ] => ∀[[y <: Σ] => isSumOf[x ∪ y, x, y]]]] =>
      val ev1 = notForall2[[x <: Σ, y <: Σ] => isSumOf[x ∪ y, x, y]](assumption)
      type X = ev1.S; type Y = ev1.value.S
      val ev2: ￢[isSumOf[X ∪ Y, X, Y]] = ev1.value.value
      val ev3: isSumOf[X ∪ Y, X, Y] = byContradiction { assumption3: ∃[[w <: Σ] => ￢[(w ∈ (X ∪ Y)) <=> ((w ∈ X) ∨ (w ∈ Y))]] =>
        type W = assumption3.S
        val ev31: ￢[(W ∈ (X ∪ Y)) <=> ((W ∈ X) ∨ (W ∈ Y))] = assumption3.value
        val ev32: (W ∈ (X ∪ Y)) => ((W ∈ X) ∨ (W ∈ Y)) = { assumption32 =>
          val ev321: ∃[[z <: Σ] => ((W ∈ z) ∧ (z ∈ (X ++: Y)))] = unionSet.constraint2[X ++: Y, W].implies(assumption32)
          type Z = ev321.S
          val ev322: W ∈ Z = ev321.value._1
          val ev323: Z ∈ (X ++: Y) = ev321.value._2
          val ev324: (Z =::= X) ∨ (Z =::= Y) = pairSet.constraint2[Z, X, Y].implies(ev323)
          ev324 match {
            case zEqX: (Z =::= X) => Left(zEqX.sub(ev322))
            case zEqY: (Z =::= Y) => Right(zEqY.sub(ev322))
          }
        }
        val ev33: ((W ∈ X) ∨ (W ∈ Y)) => (W ∈ (X ∪ Y)) = { assumption33 =>
          val ev331: ∃[[z <: Σ] => ((W ∈ z) ∧ (z ∈ (X ++: Y)))] = assumption33 match {
            case wInX: (W ∈ X) => forType[X].generalize(wInX ∧ pairSet.containsLeft)
            case wInY: (W ∈ Y) => forType[Y].generalize(wInY ∧ pairSet.containsRight)
          }
          unionSet.constraint2[X ++: Y, W].impliedBy(ev331)
        }
        val ev34: (W ∈ (X ∪ Y)) <=> ((W ∈ X) ∨ (W ∈ Y)) = ev32 ∧ ev33
        ev34 ∧ ev31
      }
      ev3 ∧ ev2
    }
  }

  def constraint[x <: Σ, y <: Σ]: isSumOf[x ∪ y, x, y] = forType2[x, y].instantiate[[x1 <: Σ, y1 <: Σ] => isSumOf[x1 ∪ y1, x1, y1]](constraintValue)

  def constraint2[x <: Σ, X <: Σ, Y <: Σ]: (x ∈ (X ∪ Y)) <=> ((x ∈ X) ∨ (x ∈ Y)) = {
    forType[x].instantiate[[w <: Σ] => (w ∈ (X ∪ Y)) <=> (w ∈ X) ∨ (w ∈ Y)](constraint[X, Y])
  }

  def commute[X <: Σ, Y <: Σ]: (X ∪ Y) =::= (Y ∪ X) = {
    val ev1: ∀[[x <: Σ] => (x ∈ (X ∪ Y)) <=> (x ∈ (Y ∪ X))] = byContradiction { assumption: ∃[[x <: Σ] => ￢[(x ∈ (X ∪ Y)) <=> (x ∈ (Y ∪ X))]] =>
      type X1 = assumption.S
      val ev11: ￢[(X1 ∈ (X ∪ Y)) <=> (X1 ∈ (Y ∪ X))] = assumption.value
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

  def includesLeft[X <: Σ, Y <: Σ]: X ⊂ (X ∪ Y) = byContradiction { assumption: ∃[[x <: Σ] => ￢[(x ∈ X) => (x ∈ (X ∪ Y))]] =>
    type X1 = assumption.S
    val ev1: ￢[(X1 ∈ X) => (X1 ∈ (X ∪ Y))] = assumption.value
    val ev2: (X1 ∈ X) => (X1 ∈ (X ∪ Y)) = { x1InX => constraint2[X1, X, Y].impliedBy(Left(x1InX)) }
    ev2 ∧ ev1
  }

  def includesRight[X <: Σ, Y <: Σ]: Y ⊂ (X ∪ Y) = commute[Y, X].sub(includesLeft[Y, X])

  def containsLeft[x <: Σ, X <: Σ, Y <: Σ]: (x ∈ X) => (x ∈ (X ∪ Y)) = {
    forType[x].instantiate[[x1 <: Σ] => (x1 ∈ X) => (x1 ∈ (X ∪ Y))](includesLeft[X, Y])
  }

  def containsRight[y <: Σ, X <: Σ, Y <: Σ]: (y ∈ Y) => (y ∈ (X ∪ Y)) = {
    commute[Y, X].sub[[xy <: Σ] => (y ∈ Y) => (y ∈ xy)](containsLeft[y, Y, X])
  }

}
