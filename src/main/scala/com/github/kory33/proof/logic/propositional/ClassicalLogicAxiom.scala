package com.github.kory33.proof.logic.propositional

import com.github.kory33.proof.logic.propositional.LogicDefinitions.￢

/**
  * axiom set that adds elimination of double negation
  */
trait ClassicalLogicAxiom {

  def eliminateDoubleNegation[A]: ￢[￢[A]] => A

}
