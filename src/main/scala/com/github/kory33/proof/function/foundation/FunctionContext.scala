package com.github.kory33.proof.function.foundation

import scala.language.implicitConversions
import scala.reflect.Selectable.reflectiveSelectable

import com.github.kory33.proof.logic.predicate._
import com.github.kory33.proof.logic.predicate.Equality._

trait FunctionContext extends PredicateLogicContext {
  val domCtx: PredicateLogicContext

  type InCod[_]
  type InDom = domCtx.Univ

  // application
  type $_:[_, _]

  // "cross contextual" composition
  type after[g, f]

  type codEq[A, B] = Equality[InCod, A, B]

  implicit def application[f: Univ, x: InDom]: InCod[f $_: x]

  type Lambda[F[_]]
  type Functional[F[_]] = domCtx.∀[[x] => InCod[F[x]]]
  implicit def lift[F[_]: Functional]: Univ[Lambda[F]]
  implicit def liftApply[F[_]: Functional, x: InDom]: (Lambda[F] $_: x) codEq F[x]

  def composition[g, f](
    ctx1: FunctionContext { type InDom = FunctionContext.this.InDom },
    ctx2: FunctionContext { type InCod = FunctionContext.this.InCod }
  )(implicit ev1: ctx1.Univ[f], ev2: ctx2.Univ[g]): Univ[g after f]

  def compositionEq[g, f, x: InDom](
    ctx1: FunctionContext { type InDom = FunctionContext.this.InDom },
    ctx2: FunctionContext { type InCod = FunctionContext.this.InCod }
  )(implicit ev1: ctx1.Univ[f], ev2: ctx2.Univ[g]): ((g after f) $_: x) codEq (ctx2.$_:[g, ctx1.$_:[f, x]])

  def extensionality[f, g](extension: domCtx.∀[[x] => (f $_: x) codEq (g $_: x)]): f =::= g
}

trait EndoFunctionContext extends FunctionContext {
  val domCtx: PredicateLogicContext { type Univ = InCod }

  type codEq[A, B] = Equality[InCod, A, B]

  implicit def endoComposition[g: Univ, f: Univ]: Univ[g after f] = composition[g, f](this, this)
  implicit def endoCompositionEq[g: Univ, f: Univ, x: InDom]: ((g after f) $_: x) codEq (g $_: f $_: x) = compositionEq[g, f, x](this, this)

  implicit def compositionAssoc[f: Univ, g: Univ, h: Univ]: ((h after g) after f) =::= (h after (g after f)) = {
    val ev1: domCtx.∀[[x] => (((h after g) after f) $_: x) codEq ((h after (g after f)) $_: x)] = {
      domCtx.genUniv { xw: domCtx.OWrap => type x = xw.T
        implicit val xD: domCtx.Univ[x] = xw.obj
        val ev11: (((h after g) after f) $_: x) codEq (h $_: g $_: f $_: x) = endoCompositionEq[h after g, f, x].andThen(endoCompositionEq[h, g, f $_: x])
        val ev12: ((h after (g after f)) $_: x) codEq (h $_: g $_: f $_: x) = {
          val ev121: ((h after (g after f)) $_: x) codEq (h $_: (g after f) $_: x) = endoCompositionEq[h, g after f, x]
          val ev122: (h $_: (g after f) $_: x) codEq (h $_: g $_: f $_: x) = {
            endoCompositionEq[g, f, x].sub[[gfx] => (h $_: (g after f) $_: x) codEq (h $_: gfx)](universeEquality)
          }
          ev121.andThen(ev122)
        }
        ev11.andThen(ev12.commute)
      }
    }
    extensionality(ev1)
  }
}

/**
 * A context for function that gives access to the "next" arity;
 * Given that this context represents A -> B, it gives access to context of A -> (A -> B).
 */
trait MultiarityFunctionContext extends FunctionContext {
  type NextArityContext = MultiarityFunctionContext {
    type InDom = MultiarityFunctionContext.this.InDom
    type InCod = MultiarityFunctionContext.this.Univ
  }

  def nextArity: NextArityContext
}

/**
 * A context for function that gives access to the next arity with arbitrary domain.
 * Given that this context represents A -> B, it gives access to context of C -> (A -> B).
 */
trait ExponentiableFunctionContext extends MultiarityFunctionContext {
  type NextArityContextOnDom[Dom[_]] = ExponentiableFunctionContext {
    type InDom = Dom
    type InCod = ExponentiableFunctionContext.this.Univ
  }

  def nextArityWithDom[Dom[_]]: NextArityContextOnDom[Dom]
  def nextArity: NextArityContextOnDom[InDom] = nextArityWithDom[InDom]
}
