package com.github.kory33.proof.function

import com.github.kory33.proof.function.foundation._

trait ConstantFunction {
  val context: FunctionContext

  import context._

  type λ = Lambda

  type Constant[x] = λ[[z] => x]
  implicit def constantLambdaFunctional[x: InCod]: Functional[[z] => x] = domCtx.genUniv { _ => implicitly }
  implicit def constantLift[x: InCod]: Univ[Constant[x]] = lift
  implicit def constantApply[x: InCod, z: InDom]: (Constant[x] $_: z) codEq x = liftApply
}
