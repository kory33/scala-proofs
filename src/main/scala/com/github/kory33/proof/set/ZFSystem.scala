package com.github.kory33.proof.set

import com.github.kory33.proof.logic.predicate.PredicateLogicDefinitions.{∃, _}
import com.github.kory33.proof.logic.predicate.PredicateLogicSystem._
import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set.ZFAxiom._

object ZFSystem {
  /**
    * There exists an empty set.
    */
  def existsEmpty(implicit axiom: ZFAxiom): ∃[isEmpty] = {
    val separated = separation[[_, _] => Nothing]
    val set = existence

    type Set = set.S

    val emptyExistence: ∃[[y] => ∀[[u] => (u ∈ y) ≣ ((u ∈ Set) ∧ Nothing)]] =
      forType[Nothing].instantiate[[p] => ∃[[y] => ∀[[u] => (u ∈ y) ≣ ((u ∈ Set) ∧ Nothing)]]](
        forType[Set].instantiate[[x] => ∀[[p] => ∃[[y] => ∀[[u] => (u ∈ y) ≣ ((u ∈ x) ∧ Nothing)]]]](separated)
      )

    type EmptySet = emptyExistence.S
    val ev1: ∀[[u] => (u ∈ EmptySet) ≣ ((u ∈ Set) ∧ Nothing)] = emptyExistence.value
    val ev2: ∀[[u] => (u ∈ EmptySet) => Nothing] = byContradiction { assumption: ∃[[u] => ￢[u ∈ EmptySet] => Nothing] =>
      type U = assumption.S
      val ev21 = assumption.value
      val ev22 = forType[U].instantiate[[u] => (u ∈ EmptySet) ≣ ((u ∈ Set) ∧ Nothing)](ev1)
      val ev23 = ev22.implies.andThen { conclusion: (U ∈ Set) ∧ Nothing => conclusion._2 }
      ev21(ev23)
    }
    val ev3: ∀[[u] => u ∉ EmptySet] = ev2
  
    forType[EmptySet].generalize[[x] => ∀[[y] => y ∉ x]](ev3)
  }
}