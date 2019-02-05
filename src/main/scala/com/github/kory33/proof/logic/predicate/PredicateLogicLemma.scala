package com.github.kory33.proof.logic.predicate

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.logic.propositional.ClassicalLogicSystem._

trait PredicateLogicLemma {
  val language: PredicateLanguage

  import language._

  def predicateDeMorgan1[F[_]]: ∀[F] <=> ￢[∃[[x] => ￢[F[x]]]] = ???
  def predicateDeMorgan2[F[_]]: ∃[F] <=> ￢[∀[[x] => ￢[F[x]]]] = ???
  def predicateDeMorgan3[F[_]]: ∀[[x] => ￢[F[x]]] <=> ￢[∃[F]] = predicateDeMorgan2[F].negSides.andThen(doubleNegationEquivalence.commute).commute
}
