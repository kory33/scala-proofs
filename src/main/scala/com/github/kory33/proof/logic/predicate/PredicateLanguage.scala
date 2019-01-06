package com.github.kory33.proof.logic.predicate

import com.github.kory33.proof.logic.propositional.LogicDefinitions._

trait PredicateLanguage {
    type Obj <: AnyRef

    trait Exists[F[_]] {
        val witness: Obj
        val proof: F[witness.type]
    }

    type Forall[F[_]] = (Obj => Any) { def apply(x: Obj): F[x.type] }
}
