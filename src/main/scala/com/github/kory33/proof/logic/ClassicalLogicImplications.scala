package com.github.kory33.proof.logic

import com.github.kory33.proof.logic.LogicDefinitions.￢

object ClassicalLogicImplications {

  implicit def eliminateDoubleNegation[A](implicit axiom: ClassicalLogicAxiom): ￢[￢[A]] => A = {
    axiom.eliminateDoubleNegation
  }

}
