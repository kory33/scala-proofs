package com.github.kory33.proof.set.zf

import scala.language.implicitConversions

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.logic.propositional.ClassicalLogicSystem._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateSystem._
import com.github.kory33.proof.set.logic.SetDomain
import com.github.kory33.proof.logic.predicate.Equality._
import com.github.kory33.proof.set.zf.operators._
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set.Universal._
import com.github.kory33.proof.set._

class RelationConstruct(val cartesianProduct: CartesianProductConstruct) {

  val comprehension: cartesianProduct.comprehension.type = cartesianProduct.comprehension
  val orderedPair: cartesianProduct.orderedPair.type = cartesianProduct.orderedPair
  type Comprehension = comprehension.Comprehension

  type ::: = cartesianProduct.:::
  type × = cartesianProduct.×

  /**
   * Typeclass on relation; R is a relation on X and Y
   */
  trait Relation[R, X, Y] {
    val subsetOfProduct: R ⊂ (X × Y)

    type dom = Comprehension[X, [x] => Y hasSome ([y] => (x ::: y) ∈ R)]
    type range = Comprehension[Y, [y] => X hasSome ([x] => (x ::: y) ∈ R)]
  }

  type Endorelation[R, X] = Relation[R, X, X]

  /**
   * R is a reflexive relation on X
   */
  trait ReflexiveRelation[R : SetDomain, X] extends Endorelation[R, X] {
    val reflexivity: X hasAll ([x] => (x ::: x) ∈ R)
    def reflexive[x : SetDomain](implicit domain: x ∈ X): (x ::: x) ∈ R = forType[x].instantiate[[x] => (x ∈ X) => (x ::: x) ∈ R](reflexivity)(domain)
  }

  /**
   * R is a symmetric relation on X
   */
  trait SymmetricRelation[R, X] extends Endorelation[R, X] {
    val symmetry: X hasAll ([x] => X hasAll ([y] => (x ::: y) ∈ R => (y ::: x) ∈ R))
    def symmetric[x : SetDomain, y : SetDomain](xRy: (x ::: y) ∈ R)(implicit domain1: x ∈ X, domain2: y ∈ X): (y ::: x) ∈ R = {
      val ev1 = forType[x].instantiate[[x1] => (x1 ∈ X) => (X hasAll ([y] => (x1 ::: y) ∈ R => (y ::: x1) ∈ R))](symmetry)(domain1)
      val ev2 = forType[y].instantiate[[y1] => (y1 ∈ X) => (x ::: y1) ∈ R => (y1 ::: x) ∈ R](ev1)(domain2)
      ev2(xRy)
    }
  }

  /**
   * R is a transitive relation on X
   */
  trait TransitiveRelation[R, X] extends Endorelation[R, X] {
    val transition: X hasAll ([x] => X hasAll ([y] => X hasAll ([z] => ((x ::: y) ∈ R) ∧ ((y ::: z) ∈ R) => (x ::: z) ∈ R)))
    def transitive[x : SetDomain, y : SetDomain, z : SetDomain](xRy: (x ::: y) ∈ R, yRz: (y ::: z) ∈ R)(implicit domain1: x ∈ X, domain2: y ∈ X, domain3: z ∈ X): (x ::: z) ∈ R = {
      val ev1 = forType[x].instantiate[[x1] => (x1 ∈ X) => X hasAll ([y] => X hasAll ([z] => ((x1 ::: y) ∈ R) ∧ ((y ::: z) ∈ R) => (x1 ::: z) ∈ R))](transition)(domain1)
      val ev2 = forType[y].instantiate[[y1] => (y1 ∈ X) => X hasAll ([z] => ((x ::: y1) ∈ R) ∧ ((y1 ::: z) ∈ R) => (x ::: z) ∈ R)](ev1)(domain2)
      val ev3 = forType[z].instantiate[[z1] => (z1 ∈ X) => ((x ::: y) ∈ R) ∧ ((y ::: z1) ∈ R) => (x ::: z1) ∈ R](ev2)(domain3)
      ev3(xRy ∧ yRz)
    }
  }

  /**
   * R is an equivalence relation on X.
   */
  trait EquivalenceRelation[R, X] extends ReflexiveRelation[R, X] with SymmetricRelation[R, X] with TransitiveRelation[R, X]

  trait AntisymmetricRelation[R, X] extends Endorelation[R, X] {
    val antisymmetry: X hasAll ([x] => X hasAll ([y] => ((x ::: y) ∈ R) ∧ ((y ::: x) ∈ R) => x =::= y))
    def antisymmetric[x : SetDomain, y : SetDomain](xRy: (x ::: y) ∈ R, yRx: (y ::: x) ∈ R)
                                                    (implicit domain1: x ∈ X, domain2: y ∈ X): ((x ::: y) ∈ R) ∧ ((y ::: x) ∈ R) => x =::= y = {
      val ev1 = forType[x].instantiate[[x1] => (x1 ∈ X) => X hasAll ([y] => ((x1 ::: y) ∈ R) ∧ ((y ::: x1) ∈ R) => x1 =::= y)](antisymmetry)(domain1)
      val ev2 = forType[y].instantiate[[y1] => (y1 ∈ X) => ((x ::: y1) ∈ R) ∧ ((y1 ::: x) ∈ R) => x =::= y1](ev1)(domain2)
      ev2
    }
  }

  trait PartialOrder[R, X] extends ReflexiveRelation[R, X] with TransitiveRelation[R, X] with AntisymmetricRelation[R, X]

  trait ConnectedRelation[R, X] extends Endorelation[R, X] {
    val connection: X hasAll ([x] => X hasAll ([y] => ((x ::: y) ∈ R) ∨ ((y ::: x) ∈ R)))
    def connected[x : SetDomain, y : SetDomain](implicit domain1: x ∈ X, domain2: y ∈ X): ((x ::: y) ∈ R) ∨ ((y ::: x) ∈ R) = {
      val ev1 = forType[x].instantiate[[x1] => (x1 ∈ X) => X hasAll ([y] => ((x1 ::: y) ∈ R) ∨ ((y ::: x1) ∈ R))](connection)(domain1)
      val ev2 = forType[y].instantiate[[y1] => (y1 ∈ X) => ((x ::: y1) ∈ R) ∨ ((y1 ::: x) ∈ R)](ev1)(domain2)
      ev2
    }
  }

  trait LinearOrder[R, X] extends PartialOrder[R, X] with ConnectedRelation[X, R]

  /**
   * Relation R on X and Y is left-unique.
   * for all x1, x2 ∈ X and y ∈ Y, x1Ry ∧ x2Ry => x1 = x2
   */
  trait LeftUniqueRelation[R, X, Y] extends Relation[R, X, Y] {
    val uniquePreimage: (X hasAll ([x1] => X hasAll ([x2] => Y hasAll ([y] => ((x1 ::: y) ∈ R) ∧ ((x2 ::: y) ∈ R) => (x1 =::= x2)))))
  }

  /**
   * Relation R on X and Y is right-unique. That is, R is a partial function on X and Y.
   * for all x ∈ X and y1, y2 ∈ Y, xRy1 ∧ xRy2 => y1 = y2
   */
  trait PartialFunction[R, X, Y] extends Relation[R, X, Y] {
    val uniqueImage: (X hasAll ([x] => Y hasAll ([y1] => Y hasAll ([y2] => ((x ::: y1) ∈ R) ∧ ((x ::: y2) ∈ R) => (y1 =::= y2)))))
  }

  /**
   * Relation R on X and Y is one-to-one
   */
  trait OneToOneRelation[R, X, Y] extends LeftUniqueRelation[R, X, Y] with PartialFunction[R, X, Y]

  /**
   * Relation R on X and Y is left-total. That is, dom(R) = X.
   */
  trait LeftTotalRelation[R, X, Y] extends Relation[R, X, Y] {
    val domEqDomain: dom =::= X
  }

  /**
   * Relation R on X and Y is right-total, or surjective. That is, range(R) = Y.
   */
  trait SurjectiveRelation[R, X, Y] extends Relation[R, X, Y] {
    val rangeEqCod: range =::= Y
  }

  /**
   * Relation F on X and Y is a function.
   */
  trait Function[F, X : SetDomain, Y : SetDomain] extends LeftTotalRelation[F, X, Y] with PartialFunction[F, X, Y] {
    trait apply[x](val xInX: x ∈ X) {
      /** application result */
      type a = ∃[[y] => (x ::: y) ∈ F]#S
    }

    /**
     * image of a subset of domain
     */
    trait image[A](val aIncludedInX: A ⊂ X) {
      type i = Comprehension[Y, [y] => A hasSome ([x] => y =::= apply[x]#a)]
    }

    /**
     * preimage of an elemnt in range
     */
    trait preimage[y](val yInRange: y ∈ range) {
      type p = Comprehension[X, [x] => y =::= apply[x]#a]
    }

    /**
     * for all x in X, xF(F(x))
     */
    val valueConstraint1: X hasAll ([x] => (x ::: apply[x]#a) ∈ F) = {
      ???
    }

    /**
     * application of an elemnt in domain belongs to range
     */
    val valueConstraint2: X hasAll ([x] => apply[x]#a ∈ range) = {
      import orderedPair.setDomain

      byContradiction { implicit assumption: ∃[[x] => ￢[(x ∈ X) => (apply[x]#a ∈ range)]] =>
        type Z = assumption.S
        implicit val applicationIsSet: SetDomain[apply[Z]#a] = ???

        val ev1: ￢[(Z ∈ X) => (apply[Z]#a ∈ range)] = assumption.instance
        val ev2: (Z ∈ X) => (apply[Z]#a ∈ range) = { zInX =>
          val ev21: (Z ::: apply[Z]#a) ∈ F = forType[Z].instantiate[[x] => (x ∈ X) => ((x ::: apply[x]#a) ∈ F)](valueConstraint1)(zInX)
          val ev22: (Z ::: apply[Z]#a) ∈ (X × Y) = subsetOfProduct.containsElement[Z ::: apply[Z]#a](ev21)
          val ev23: apply[Z]#a ∈ Y = cartesianProduct.rightProjection[Z, apply[Z]#a, X, Y](ev22)
          val ev24: X hasSome ([x] => (x ::: apply[Z]#a) ∈ F) = forType[Z].generalize(zInX ∧ ev21)
          val ev25: (apply[Z]#a ∈ range) <=> ((apply[Z]#a ∈ Y) ∧ (X hasSome ([x] => (x ::: apply[Z]#a) ∈ F))) = {
            comprehension.constraint2[Y, [y1] => X hasSome ([x1] => (x1 ::: y1) ∈ F), apply[Z]#a]
          }
          ev25.impliedBy(ev23 ∧ ev24)
        }
        ev2 ∧ ev1
      }
    }

    /**
     * preimage of an element in range is nonempty
     */
    val valueConstraint3: range hasAll ([y] => isNonEmpty[preimage[y]#p]) = {
      ???
    }

  }

  type Endofunction[F, X] = Function[F, X, X]

  /**
   * Function F from X into Y is a surjective function.
   */
  trait SurjectiveFunction[F, X, Y] extends Function[F, X, Y] with SurjectiveRelation[F, X, Y]

  /**
   * Function F from X into Y is an injective function.
   */
  trait InjectiveFunction[F, X, Y] extends Function[F, X, Y] with LeftUniqueRelation[F, X, Y]

  /**
   * Function F from X into Y is a bijection.
   */
  trait BijectiveFunction[F, X, Y] extends SurjectiveFunction[F, X, Y] with InjectiveFunction[F, X, Y]

  /**
   * * is a binary operation on S
   */
  trait BinaryOperation[*, S] extends Function[*, S × S, S]
}
