package com.github.kory33.proof.set

import scala.language.implicitConversions
import scala.reflect.Selectable.reflectiveSelectable

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.logic.propositional.ClassicalLogicSystem._
import com.github.kory33.proof.logic.predicate.PredicateLogicLemma
import com.github.kory33.proof.set.foundation.ZF

class EmptySet(implicit val axiom: ZF.Existence & ZF.Extensionality & ZF.Separation) {
  type L = axiom.language.type

  val basicPredicates = new BasicPredicates { val language: L = axiom.language }
  val predLemma: PredicateLogicLemma { val language: L } = new PredicateLogicLemma { val language: L = axiom.language }

  import basicPredicates._
  import predLemma._
  import ZF._
  import axiom.language._

  val emptyExistence: ∃[isEmpty] = {
    implicit val ev1: axiom.language.∃[[x] => x =::= x] = existence
    type S = ev1.witness.type
    val s: S = ev1.witness
    val ev2: ∀[[x] => ∃[[y] => ∀[[u] => (u ∈ y) <=> ((u ∈ x) ∧ Nothing)]]] = separation[[x] => Nothing]
    val ev3: ∃[[y] => ∀[[u] => (u ∈ y) <=> ((u ∈ S) ∧ Nothing)]] = ev2(s)
    type Y = ev3.witness.type
    val y: Y = ev3.witness
    val ev4: ∀[[u] => (u ∈ Y) <=> ((u ∈ S) ∧ Nothing)] = ev3.proof
    val ev5: ∀[[u] => ￢[u ∈ Y]] = { u: Any => implicit uT: Univ[u.type] =>
      val ev51: (u.type ∈ Y) <=> ((u.type ∈ S) ∧ Nothing) = ev4(u)
      val ev52: ￢[u.type ∈ Y] = { uInY: u.type ∈ Y => ev51.implies(uInY)._2 }
      ev52
    }
    genExist(y)(ev3.term, ev5)
  }

  val emptyUniqueness: Unique[isEmpty] = { x: Any => implicit xU: Univ[x.type] => y: Any => implicit yU: Univ[y.type] =>
    { assumption: (isEmpty[x.type] ∧ isEmpty[y.type]) =>
      type F = [z] => (z ∈ x.type) <=> (z ∈ y.type)
      val ev1: ∀[[z] => (z ∈ x.type) <=> (z ∈ y.type)] => (x.type =::= y.type) = extensionality(axiom)(x)(xU)(y)(yU)
      val ev2: ∀[[z] => (z ∈ x.type) <=> (z ∈ y.type)] = predicateDeMorgan1[F].impliedBy { implicit assumption2: ∃[[z] => ￢[F[z]]] =>
        val z: assumption2.witness.type = assumption2.witness
        val notFz: ￢[F[z.type]] = assumption2.proof
        val ev21: ￢[(z.type ∈ x.type) => (z.type ∈ y.type)] ∨ ￢[(z.type ∈ x.type) <= (z.type ∈ y.type)] = nonEquivalence.implies(notFz)
        val ev22: ￢[￢[(z.type ∈ x.type) => (z.type ∈ y.type)]] = introduceDoubleNeg { _ ∧ assumption._1(z) }
        val ev23: ￢[￢[(z.type ∈ x.type) <= (z.type ∈ y.type)]] = introduceDoubleNeg { _ ∧ assumption._2(z) }
        removeDisj(ev21)(ev22)(ev23)
      }
      ev1(ev2)
    }
  }

  val emptySet: emptyExistence.witness.type = emptyExistence.witness
  implicit val emptySetUniv: Univ[emptySet.type] = emptyExistence.term

}
