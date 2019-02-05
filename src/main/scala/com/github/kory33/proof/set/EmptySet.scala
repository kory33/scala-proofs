package com.github.kory33.proof.set

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
    val ev1: axiom.language.∃[[x] => x =::= x] = existence
    type S = ev1.witness.type
    val s: S = ev1.witness
    val ev2: ∀[[x] => ∃[[y] => ∀[[u] => (u ∈ y) <=> ((u ∈ x) ∧ Nothing)]]] = separation[[x] => Nothing]
    val ev3: ∃[[y] => ∀[[u] => (u ∈ y) <=> ((u ∈ S) ∧ Nothing)]] = ???
    type Y = ev3.witness.type
    val y: Y = ev3.witness
    val ev4: ∀[[u] => (u ∈ Y) <=> ((u ∈ S) ∧ Nothing)] = ev3.proof
    val ev5: ∀[[u] => ￢[u ∈ Y]] = { u: Any => implicit uT: Univ[u.type] =>
      val ev51: (u.type ∈ Y) <=> ((u.type ∈ S) ∧ Nothing) = ???
      val ev52: ￢[u.type ∈ Y] = { uInY: u.type ∈ Y => ev51.implies(uInY)._2 }
      ev52
    }
    val ev7: isEmpty[Y] = predicateDeMorgan3[[u] => u ∈ Y].implies(ev5)
    genExist(y)(ev3.term, ev7)
  }
}
