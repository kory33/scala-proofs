package com.github.kory33.proof.set.zf.operators

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateSystem._
import com.github.kory33.proof.set.logic.SetDomain
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set._

class IntersectionConstruct(val comprehension: ComprehensionConstruct, val union: UnionSetConstruct) {
  
  type Intersection[F] = comprehension.Comprehension[union.Union[F], [z] => F hasAll ([f] => z ∈ f)]

  val constraintValue: ∀[[F] => ∀[[z] => (z ∈ Intersection[F]) <=> (F hasAll ([x] => z ∈ x))]] = ???

  def constraint[F : SetDomain, z : SetDomain]: (z ∈ Intersection[F]) <=> (F hasAll ([x] => z ∈ x)) = {
    forType2[F, z].instantiate[[F1, z1] => (z1 ∈ Intersection[F1]) <=> (F1 hasAll ([x] => z1 ∈ x))](constraintValue)
  }

}

class BinaryIntersectionConstruct(val pairSet: PairSetConstruct,
                                  val intersection: IntersectionConstruct) {

  type Intersection = intersection.Intersection
  type ++: = pairSet.++:

  type ∩[x, y] = Intersection[x ++: y]
  val constraintValue: ∀[[x] => ∀[[y] => isIntersectionOf[x ∩ y, x, y]]] = ???

  def constraint[x : SetDomain, y : SetDomain]: isIntersectionOf[x ∩ y, x, y] = {
    forType2[x, y].instantiate[[x1, y1] => isIntersectionOf[x1 ∩ y1, x1, y1]](constraintValue)
  }

}
