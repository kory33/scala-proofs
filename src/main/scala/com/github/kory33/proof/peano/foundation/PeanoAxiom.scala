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
    implicit val succFn: nfn.Univ[S]
  }

  trait ZeroFirst extends PeanoAxiom {
    import context._; import nfn.$_:
    val zeroFirst: ￢[∃[[x] => (S $_: x) =::= Zero]]
  }

  trait SuccInj extends PeanoAxiom {
    import context._; import nfn.$_:
    val succInj: ∀[[x] => ∀[[y] => ((S $_: x) =::= (S $_: y)) => (x =::= y)]]
  }

  trait Induction extends PeanoAxiom {
    import context._; import nfn.$_:
    def induction[P[_]]: (P[Zero] ∧ ∀[[n] => P[n] => P[S $_: n]]) => ∀[P]
  }

  type Axioms =
    ZeroExistence &
    Succ &
    ZeroFirst &
    SuccInj &
    Induction

  def zeroExistence(implicit z: ZeroExistence) = z.zero
  def succ(implicit s: Succ) = s.succFn
  def zeroFirst(implicit z: ZeroFirst) = z.zeroFirst
  def succInj(implicit s: SuccInj) = s.succInj
  def induction[P[_]](implicit s: Induction) = s.induction[P]

}
