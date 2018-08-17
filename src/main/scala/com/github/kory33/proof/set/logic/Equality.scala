package com.github.kory33.proof.set.logic

import com.github.kory33.proof.set.Σ

object Equality {
  type =::=[A <: Σ, B <: Σ] = com.github.kory33.proof.logic.predicate.Equality.=::=[Σ, A, B]
}