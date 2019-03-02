package com.github.kory33.proof.set.foundation

import com.github.kory33.proof.logic.predicate._

trait SetTheoryContext extends ProjectiveCalculusContext { type ∈[_, _] }
trait SetAxiom { val context: SetTheoryContext }
