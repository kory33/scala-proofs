package com.github.kory33.proof.set.zf

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.logic.propositional.ClassicalLogicSystem._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateSystem._
import com.github.kory33.proof.set.logic.Equality._
import com.github.kory33.proof.set.zf.operators._
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set._

class RelationConstruct(val cartesianProduct: CartesianProductConstruct) {

  type Comprehension = cartesianProduct.Comprehension
  type ::: = cartesianProduct.:::
  type × = cartesianProduct.×

  /**
   * Typeclass on relation; R is a relation on X and Y
   */
  trait Relation[R <: Σ, X <: Σ, Y <: Σ] {
    val subset: R ⊂ (X × Y)

    type dom = Comprehension[X, [x <: Σ] => Y hasSome ([y <: Σ] => (x ::: y) ∈ R)]
    type range = Comprehension[Y, [y <: Σ] => X hasSome ([x <: Σ] => (x ::: y) ∈ R)]
  }

  type Endorelation[R <: Σ, X <: Σ] = Relation[R, X, X]

  /**
   * R is a reflexive relation on X
   */
  trait ReflexiveRelation[R <: Σ, X <: Σ] extends Endorelation[R, X] {
    val reflexivity: X hasAll ([x <: Σ] => (x ::: x) ∈ R)
    def reflexive[x <: Σ](implicit domain: x ∈ X): (x ::: x) ∈ R = forType[x].instantiate[[x <: Σ] => (x ∈ X) => (x ::: x) ∈ R](reflexivity)(domain)
  }

  /**
   * R is a symmetric relation on X
   */
  trait SymmetricRelation[R <: Σ, X <: Σ] extends Endorelation[R, X] {
    val symmetry: X hasAll ([x <: Σ] => X hasAll ([y <: Σ] => (x ::: y) ∈ R => (y ::: x) ∈ R))
    def symmetric[x <: Σ, y <: Σ](xRy: (x ::: y) ∈ R)(implicit domain1: x ∈ X, domain2: y ∈ X): (y ::: x) ∈ R = {
      val ev1 = forType[x].instantiate[[x1 <: Σ] => (x1 ∈ X) => (X hasAll ([y <: Σ] => (x1 ::: y) ∈ R => (y ::: x1) ∈ R))](symmetry)(domain1)
      val ev2 = forType[y].instantiate[[y1 <: Σ] => (y1 ∈ X) => (x ::: y1) ∈ R => (y1 ::: x) ∈ R](ev1)(domain2)
      ev2(xRy)
    }
  }

  /**
   * R is a transitive relation on X
   */
  trait TransitiveRelation[R <: Σ, X <: Σ] extends Endorelation[R, X] {
    val transition: X hasAll ([x <: Σ] => X hasAll ([y <: Σ] => X hasAll ([z <: Σ] => ((x ::: y) ∈ R) ∧ ((y ::: z) ∈ R) => (x ::: z) ∈ R)))
    def transitive[x <: Σ, y <: Σ, z <: Σ](xRy: (x ::: y) ∈ R, yRz: (y ::: z) ∈ R)(implicit domain1: x ∈ X, domain2: y ∈ X, domain3: z ∈ X): (x ::: z) ∈ R = {
      val ev1 = forType[x].instantiate[[x1 <: Σ] => (x1 ∈ X) => X hasAll ([y <: Σ] => X hasAll ([z <: Σ] => ((x1 ::: y) ∈ R) ∧ ((y ::: z) ∈ R) => (x1 ::: z) ∈ R))](transition)(domain1)
      val ev2 = forType[y].instantiate[[y1 <: Σ] => (y1 ∈ X) => X hasAll ([z <: Σ] => ((x ::: y1) ∈ R) ∧ ((y1 ::: z) ∈ R) => (x ::: z) ∈ R)](ev1)(domain2)
      val ev3 = forType[z].instantiate[[z1 <: Σ] => (z1 ∈ X) => ((x ::: y) ∈ R) ∧ ((y ::: z1) ∈ R) => (x ::: z1) ∈ R](ev2)(domain3)
      ev3(xRy ∧ yRz)
    }
  }

  /**
   * R is an equivalence relation on X.
   */
  trait EquivalenceRelation[R <: Σ, X <: Σ] extends ReflexiveRelation[R, X] with SymmetricRelation[R, X] with TransitiveRelation[R, X]

  /**
   * Relation R on X and Y is left-unique.
   * for all x1, x2 ∈ X and y ∈ Y, x1Ry ∧ x2Ry => x1 = x2
   */
  trait LeftUniqueRelation[R <: Σ, X <: Σ, Y <: Σ] extends Relation[R, X, Y] {
    val uniquePreimage: (X hasAll ([x1 <: Σ] => X hasAll ([x2 <: Σ] => Y hasAll ([y <: Σ] => ((x1 ::: y) ∈ R) ∧ ((x2 ::: y) ∈ R) => (x1 =::= x2)))))
  }

  /**
   * Relation R on X and Y is right-unique. That is, R is a partial function on X and Y.
   * for all x ∈ X and y1, y2 ∈ Y, xRy1 ∧ xRy2 => y1 = y2
   */
  trait PartialFunction[R <: Σ, X <: Σ, Y <: Σ] extends Relation[R, X, Y] {
    val uniqueImage: (X hasAll ([x <: Σ] => Y hasAll ([y1 <: Σ] => Y hasAll ([y2 <: Σ] => ((x ::: y1) ∈ R) ∧ ((x ::: y2) ∈ R) => (y1 =::= y2)))))
  }

  /**
   * Relation R on X and Y is one-to-one
   */
  trait OneToOneRelation[R <: Σ, X <: Σ, Y <: Σ] extends LeftUniqueRelation[R, X, Y] with PartialFunction[R, X, Y]

  /**
   * Relation R on X and Y is left-total. That is, dom(R) = X.
   */
  trait LeftTotalRelation[R <: Σ, X <: Σ, Y <: Σ] extends Relation[R, X, Y] {
    val domEqDomain: dom =::= X
  }

  /**
   * Relation R on X and Y is right-total, or surjective. That is, range(R) = Y.
   */
  trait SurjectiveRelation[R <: Σ, X <: Σ, Y <: Σ] extends Relation[R, X, Y] {
    val rangeEqCod: range =::= Y
  }

  /**
   * Relation F on X and Y is a function.
   */
  trait Function[F <: Σ, X <: Σ, Y <: Σ] extends LeftTotalRelation[F, X, Y] with PartialFunction[F, X, Y]

  type Endofunction[F <: Σ, X <: Σ] = Function[F, X, X]

  /**
   * Function F from X into Y is a surjective function.
   */
  trait SurjectiveFunction[F <: Σ, X <: Σ, Y <: Σ] extends Function[F, X, Y] with SurjectiveRelation[F, X, Y]

  /**
   * Function F from X into Y is an injective function.
   */
  trait InjectiveFunction[F <: Σ, X <: Σ, Y <: Σ] extends Function[F, X, Y] with LeftUniqueRelation[F, X, Y]

  /**
   * Function F from X into Y is a bijection.
   */
  trait BijectiveFunction[F <: Σ, X <: Σ, Y <: Σ] extends SurjectiveFunction[F, X, Y] with InjectiveFunction[F, X, Y]

}
