package com.github.kory33.proof.set.foundation

import com.github.kory33.proof.logic.predicate._

trait SetTheoryLanguage extends ProjectiveCalculusLanguage { type ∈[_, _] }
trait SetAxiom { val language: SetTheoryLanguage }