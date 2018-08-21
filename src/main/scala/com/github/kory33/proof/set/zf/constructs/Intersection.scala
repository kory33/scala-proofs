package com.github.kory33.proof.set.zf.constructs

import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateSystem._
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set._

class IntersectionConstruct(val comprehension: ComprehensionConstruct, val union: UnionSetConstruct) {
  
  type Intersection[F <: Σ] = comprehension.Comprehension[union.Union[F], [z <: Σ] => F hasSome ([f <: Σ] => z ∈ f)]

  val constraintValue: ∀[[F <: Σ] => ∀[[z <: Σ] => (z ∈ Intersection[F]) <=> (F hasAll ([x <: Σ] => z ∈ x))]] = ???

  def constraint[F <: Σ, z <: Σ]: (z ∈ Intersection[F]) <=> (F hasAll ([x <: Σ] => z ∈ x)) = {
    forType2[F, z].instantiate[[F1 <: Σ, z1 <: Σ] => (z1 ∈ Intersection[F1]) <=> (F1 hasAll ([x <: Σ] => z1 ∈ x))](constraintValue)
  }

}

class BinaryIntersectionConstruct(val pairSet: PairSetConstruct,
                                  val intersection: IntersectionConstruct) {

  type Intersection = intersection.Intersection
  type ++: = pairSet.++:

  type ∩[x <: Σ, y <: Σ] = Intersection[x ++: y]
  val constraintValue: ∀[[x <: Σ] => ∀[[y <: Σ] => isIntersectionOf[x ∩ y, x, y]]] = ???

  def constraint[x <: Σ, y <: Σ]: isIntersectionOf[x ∩ y, x, y] = {
    forType2[x, y].instantiate[[x1 <: Σ, y1 <: Σ] => isIntersectionOf[x1 ∩ y1, x1, y1]](constraintValue)
  }

}
