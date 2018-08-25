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

  /**
   * R is a reflexive relation on X
   */
  trait ReflexiveRelation[R <: Σ, X <: Σ] extends Relation[R, X, X] {
    val reflexivity: X hasAll ([x <: Σ] => (x ::: x) ∈ R)
    def reflexive[x <: Σ](implicit domain: x ∈ X): (x ::: x) ∈ R = forType[x].instantiate[[x <: Σ] => (x ∈ X) => (x ::: x) ∈ R](reflexivity)(domain)
  }

  /**
   * R is a symmetric relation on X
   */
  trait SymmetricRelation[R <: Σ, X <: Σ] extends Relation[R, X, X] {
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
  trait TransitiveRelation[R <: Σ, X <: Σ] extends Relation[R, X, X] {
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

  trait PartialFunction[R <: Σ, X <: Σ, Y <: Σ] extends Relation[R, X, Y] {
    val uniqueImage: (X hasAll ([x <: Σ] => Y hasAll ([y1 <: Σ] => Y hasAll ([y2 <: Σ] => ((x ::: y1) ∈ R) ∧ ((x ::: y2) ∈ R) => (y1 =::= y2)))))
  }

  trait Function[F <: Σ, X <: Σ, Y <: Σ]{
    def definitionEqDomain(partialFunction: PartialFunction[F, X, Y]): partialFunction.dom =::= X
  }

}
