package com.github.kory33.proof.logic

import com.github.kory33.proof.logic.LogicDefinitions.￢

/**
  * axiom set that adds elimination of double negation
  */
trait ClassicalLogicAxiom {

  def eliminateDoubleNegation[A]: ￢[￢[A]] => A

}
