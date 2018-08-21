package com.github.kory33.proof.set.zf.constructs

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
    byContradiction { assumption: ∃[[z <: Σ] => ￢[∀[[x <: Σ] => ∀[[y <: Σ] => (x isUnionOf z) ∧ (y isUnionOf z) => x =::= y]]]] =>
      type Z = assumption.S
      val ev1: ∃[[x <: Σ] => ￢[∀[[y <: Σ] => (x isUnionOf Z) ∧ (y isUnionOf Z) => x =::= y]]] = assumption.value
      type X = ev1.S
      val ev2: ∃[[y <: Σ] => ￢[(X isUnionOf Z) ∧ (y isUnionOf Z) => X =::= y]] = ev1.value
      type Y = ev2.S
      val ev3: ￢[(X isUnionOf Z) ∧ (Y isUnionOf Z) => X =::= Y] = ev2.value
      val ev4: (X isUnionOf Z) ∧ (Y isUnionOf Z) => X =::= Y = equivalence[X, Y, [x <: Σ] => ∃[[Y <: Σ] => ((x ∈ Y) ∧ (Y ∈ Z))]]
      ev4 ∧ ev3
    }
  }

  val unionFunctionExistence: ∃~>[[Union[_ <: Σ] <: Σ] => ∀[[x <: Σ] => Union[x] isUnionOf x]] = {
    createUnaryClassFunction[isUnionOf](uniqueExistence[isUnionOf](existence, uniqueness))
  }

  type Union[x <: Σ] = unionFunctionExistence.F[x]
  val constraint: ∀[[x <: Σ] => Union[x] isUnionOf x] = unionFunctionExistence.value

}

class BinaryUnionConstruct(val pairSet: PairSetConstruct,
                           val unionSet: UnionSetConstruct) {

  type Union = unionSet.Union
  type ++: = pairSet.++:

  type ∪[x <: Σ, y <: Σ] = Union[x ++: y]
  val constraintValue: ∀[[x <: Σ] => ∀[[y <: Σ] => isSumOf[x ∪ y, x, y]]] = ???
  def constraint[x <: Σ, y <: Σ]: isSumOf[x ∪ y, x, y] = forType2[x, y].instantiate[[x1 <: Σ, y1 <: Σ] => isSumOf[x1 ∪ y1, x1, y1]](constraintValue)

}
