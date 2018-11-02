package com.github.kory33.proof.set.axiom.zf

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.logic.predicate.Equality._
import com.github.kory33.proof.set._
import com.github.kory33.proof.set.SetDefinitions._

/**
  * Axiom schema of replacement.
  *
  * For every class function F, there exists a the range F[A] = {F(x): x ∈ A} of F.
  */
trait ZFReplacement {
  def replacement[F[_]]: ∀[[A] => ∃[[FA] => isRangeOfClassFn[FA, F, A]]]
}
