package com.github.kory33.proof.logic.predicate

import scala.language.implicitConversions
import scala.reflect.Selectable.reflectiveSelectable

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.logic.propositional.ClassicalLogicSystem._

trait PredicateLogicLemma {
  val language: PredicateLanguage

  import language._

  implicit def existenceUniv[F[_]](implicit ex: ∃[F]): Univ[ex.witness.type] = ex.term

  def predicateDeMorgan1[F[_]]: ∀[F] <=> ￢[∃[[x] => ￢[F[x]]]] = {
    val ev1: ∀[F] => ￢[∃[[x] => ￢[F[x]]]] = { allF: ∀[F] => implicit assumption: ∃[[x] => ￢[F[x]]] =>
      val x: assumption.witness.type = assumption.witness
      val ev1: ￢[F[x.type]] = assumption.proof
      val ev2: F[x.type] = allF(x)
      ev2 ∧ ev1
    }
    val ev2: ∀[F] <= ￢[∃[[x] => ￢[F[x]]]] = { nonExistence: ￢[∃[[x] => ￢[F[x]]]] => 
      { x: Any => implicit xUniv: Univ[x.type] =>
        eliminateDoubleNegation { notFx: ￢[F[x.type]] =>
          val ev21: ∃[[x] => ￢[F[x]]] = genExist(x)(xUniv, notFx)
          ev21 ∧ nonExistence
        }
      }
    }
    ev1 ∧ ev2
  }

  def predicateDeMorgan2[F[_]]: ∃[F] <=> ￢[∀[[x] => ￢[F[x]]]] = {
    val ev1: ∃[F] => ￢[∀[[x] => ￢[F[x]]]] = { implicit existence: ∃[F] => universality: ∀[[x] => ￢[F[x]]] =>
      val x: existence.witness.type = existence.witness
      existence.proof ∧ universality(x)
    }
    val ev2: ∃[F] <= ￢[∀[[x] => ￢[F[x]]]] = eliminateDoubleNegation { nonImplicationAssumption: ￢[￢[∀[[x] => ￢[F[x]]]] => ∃[F]] =>
      val (nonUniversality, nonExistence) = nonImplication.implies(nonImplicationAssumption)
      val ev21: ￢[∃[[x] => ￢[￢[F[x]]]]] = { implicit assumption21: ∃[[x] => ￢[￢[F[x]]]] =>
        val x: assumption21.witness.type = assumption21.witness
        implicit val ev211: F[x.type] = eliminateDoubleNegation(assumption21.proof)
        genExist(x) ∧ nonExistence
      }
      val ev22: ∀[[x] => ￢[F[x]]] = predicateDeMorgan1[[x] => ￢[F[x]]].impliedBy(ev21)
      ev22 ∧ nonUniversality
    }
    ev1 ∧ ev2
  }

  def predicateDeMorgan3[F[_]]: ∀[[x] => ￢[F[x]]] <=> ￢[∃[F]] = predicateDeMorgan2[F].negSides.andThen(doubleNegationEquivalence.commute).commute
}
