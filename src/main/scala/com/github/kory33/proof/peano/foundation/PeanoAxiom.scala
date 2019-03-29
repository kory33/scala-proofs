package com.github.kory33.proof.peano.foundation

import com.github.kory33.proof.logic.predicate._
import com.github.kory33.proof.logic.propositional.LogicDefinitions._

object Peano {

  sealed trait PeanoAxiom { val context: PeanoContext }

  trait ZeroExistence extends PeanoAxiom {
    import context._
    implicit val zero: Univ[Zero]
  }

  trait Succ extends PeanoAxiom {
    import context._
    implicit val succFn: Fn1[S]
  }

  trait ZeroFirst extends PeanoAxiom {
    import context._
    val zeroFirst: ￢[∃[[x] => (S[x]) =::= Zero]]
  }

  trait SuccInj extends PeanoAxiom {
    import context._
    val succInj: ∀[[x] => ∀[[y] => (S[x] =::= S[y]) => (x =::= y)]]
  }

  trait Induction extends PeanoAxiom {
    import context._
    def induction[P[_]]: (P[Zero] ∧ ∀[[n] => P[n] => P[S[n]]]) => ∀[P]
  }

  type Axioms =
    ZeroExistence &
    Succ &
    ZeroFirst &
    SuccInj &
    Induction

}
