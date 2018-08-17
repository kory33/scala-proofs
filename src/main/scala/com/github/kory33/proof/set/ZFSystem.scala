package com.github.kory33.proof.set

import scala.language.implicitConversions

import com.github.kory33.proof.set.logic.SpecializedPredicateDefinitions._
import com.github.kory33.proof.set.logic.SpecializedPredicateSystem._
import com.github.kory33.proof.set.logic._
import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.logic.propositional.IntuitionisticLogicSystem._
import com.github.kory33.proof.logic.propositional.ClassicalLogicSystem._
import com.github.kory33.proof.set.SetDefinitions._
import com.github.kory33.proof.set.ZFAxiom._

object Lemma {

  object Predicate {
    def forallEquivCommute[F[_ <: Σ], G[_ <: Σ]]: ∀[[x <: Σ] => F[x] <=> G[x]] => ∀[[x <: Σ] => G[x] <=> F[x]] = { equiv =>
      byContradiction { assumption: ∃[[x <: Σ] => ￢[G[x] <=> F[x]]] =>
        type X = assumption.S
        val ev1: ￢[G[X] <=> F[X]] = assumption.value
        val ev2: F[X] <=> G[X] = forType[X].instantiate[[x <: Σ] => F[x] <=> G[x]](equiv)
        ev2.commute ∧ ev1
      }
    }

    def forallEquivTransitive[F[_ <: Σ], G[_ <: Σ], H[_ <: Σ]]
      : (∀[[x <: Σ] => F[x] <=> G[x]], ∀[[x <: Σ] => G[x] <=> H[x]]) => ∀[[x <: Σ] => F[x] <=> H[x]] = { case (fg, gh) =>
      byContradiction { assumption: ∃[[x <: Σ] => ￢[F[x] <=> H[x]]] =>
        type X = assumption.S
        val ev1: ￢[F[X] <=> H[X]] = assumption.value
        val ev2: F[X] <=> G[X] = forType[X].instantiate[[x <: Σ] => F[x] <=> G[x]](fg)
        val ev3: G[X] <=> H[X] = forType[X].instantiate[[x <: Σ] => G[x] <=> H[x]](gh)
        ev2.andThen(ev3) ∧ ev1
      }
    }

    def forallEquivConditions[F[_ <: Σ], G[_ <: Σ], H[_ <: Σ]](fg: ∀[[x <: Σ] => F[x] <=> G[x]], hg: ∀[[x <: Σ] => H[x] <=> G[x]]): ∀[[x <: Σ] => F[x] <=> H[x]] = {
      forallEquivTransitive[F, G, H](fg, forallEquivCommute[H, G](hg))
    }
  }

  /**
   * shorthand for axiom schema of separation.
   */
  def separate[X <: Σ, F[_ <: Σ]](implicit axiom: ZFAxiom): ∃[[y <: Σ] => ∀[[u <: Σ] => (u ∈ y) <=> ((u ∈ X) ∧ F[u])]] = {
    forType[X].instantiate[[x <: Σ] => ∃[[y <: Σ] => ∀[[u <: Σ] => (u ∈ y) <=> ((u ∈ x) ∧ F[u])]]](separation[F])
  }

  /**
   * If there exists a set containing all set u such that F[u], then there exists a subset containing all u such that F[u] and nothing else.
   */
  def comprehendsExactly[F[_ <: Σ]](existsSuperSet: ∃[[y <: Σ] => ∀[[z <: Σ] => F[z] => (z ∈ y)]])(implicit axiom: ZFAxiom): ∃[[y <: Σ] => ∀[[z <: Σ] => (z ∈ y) <=> F[z]]] = {
    type Y = existsSuperSet.S
    val ev1: ∀[[u <: Σ] => F[u] => (u ∈ Y)] = existsSuperSet.value
    val ev2: ∃[[w <: Σ] => ∀[[u <: Σ] => (u ∈ w) <=> ((u ∈ Y) ∧ F[u])]] = separate[Y, F]
    type W = ev2.S
    val ev3: ∀[[u <: Σ] => (u ∈ W) <=> ((u ∈ Y) ∧ F[u])] = ev2.value
    val ev4: ∀[[u <: Σ] => (u ∈ W) <=> F[u]] = byContradiction { assumption: ∃[[u <: Σ] => ￢[(u ∈ W) <=> F[u]]] =>
      type U = assumption.S
      val ev41: ￢[(U ∈ W) <=> F[U]] = assumption.value
      val ev42: (U ∈ W) <=> ((U ∈ Y) ∧ F[U]) = forType[U].instantiate[[u <: Σ] => (u ∈ W) <=> ((u ∈ Y) ∧ F[u])](ev3)
      val ev43: (U ∈ W) => F[U] = ev42.implies.andThen(_._2)
      val ev44: F[U] => (U ∈ Y) = forType[U].instantiate[[u <: Σ] => F[u] => (u ∈ Y)](ev1)
      val ev45: F[U] => (U ∈ W) = { fu: F[U] => ev42.impliedBy(ev44(fu) ∧ fu) }
      val ev46: (U ∈ W) <=> F[U] = ev43 ∧ ev45
      ev46 ∧ ev41
    }
    forType[W].generalize[[y <: Σ] => ∀[[z <: Σ] => (z ∈ y) <=> F[z]]](ev4)
  }

  /**
   * shorthand for axiom of extensionality.
   */
  def setEquals[X <: Σ, Y <: Σ](containsSameElement: ∀[[z <: Σ] => (z ∈ X) <=> (z ∈ Y)])(implicit axiom: ZFAxiom): X =::= Y = {
    forType[Y].instantiate[[y <: Σ] => ∀[[z <: Σ] => (z ∈ X) <=> (z ∈ y)] => (X =::= y)](
      forType[X].instantiate[[x <: Σ] => ∀[[y <: Σ] => ∀[[z <: Σ] => (z ∈ x) <=> (z ∈ y)] => (x =::= y)]](extensionality)
    )(containsSameElement)
  }

  /**
   * Two sets having the same equivalence condition on their elements are equal.
   */
  def equivalence[X <: Σ, Y <: Σ, F[_ <: Σ]](implicit axiom: ZFAxiom): (∀[[w <: Σ] => (w ∈ X) <=> F[w]] ∧ ∀[[w <: Σ] => (w ∈ Y) <=> F[w]]) => (X =::= Y) = { case (x, y) =>
    val ev1: ∀[[x <: Σ] => x ∈ X <=> x ∈ Y] = Predicate.forallEquivConditions[[w <: Σ] => w ∈ X, F, [w <: Σ] => w ∈ Y](x, y)
    setEquals[X, Y](ev1)
  }

  /**
   * creates a type-level function given the that the relation is a bijection on types.
   */
  def createUnaryClassFunction[R[_ <: Σ, _ <: Σ]]
    (exists: ∀[[x <: Σ] => ∃[[y <: Σ] => y R x]],
     unique: ∀[[z <: Σ] => ∀[[x <: Σ] => ∀[[y <: Σ] => (x R z) ∧ (y R z) => x =::= y]]])
    : ∃~>[[ClassFunction[_ <: Σ] <: Σ] => ∀[[x <: Σ] => ClassFunction[x] R x]] = {
      new ∃~>[[ClassFunction[_ <: Σ] <: Σ] => ∀[[x <: Σ] => ClassFunction[x] R x]] {
        type F[x <: Σ] = ∃[[y <: Σ] => y R x]#S
        val value: ∀[[x <: Σ] => F[x] R x] = {
          byContradiction { assumption: ∃[[x <: Σ] => ￢[F[x] R x]] =>
            type X = assumption.S
            val ev1: ￢[F[X] R X] = assumption.value
            val ev2: ∃[[y <: Σ] => y R X] = forType[X].instantiate[[x <: Σ] => ∃[[y <: Σ] => y R x]](exists)
            type Y = ev2.S
            val ev3: Y R X = ev2.value
            // since the subtype of F[X] is unique to Y, they are isomorphic.
            // it is therefore safe to cast from G[Y] to G[F[X]] for any G[_].
            // let G[x] = x R X, then this cast is safe.
            val ev4: F[X] R X = ev3.asInstanceOf[F[X] R X]
            ev4 ∧ ev1
          }
        }
      }
    }

  def createBinaryClassFunction[R[_ <: Σ, _ <: Σ, _ <: Σ]]
    (exists: ∀[[x <: Σ] => ∀[[y <: Σ] => ∃[[z <: Σ] => R[z, x, y]]]],
     unique: ∀[[z <: Σ] => ∀[[w <: Σ] => ∀[[x <: Σ] => ∀[[y <: Σ] => (R[z, x, y] ∧ R[w, x, y]) => z =::= w]]]])
    : ∃~~>[[ClassFunction[_ <: Σ, _ <: Σ] <: Σ] => ∀[[x <: Σ] => ∀[[y <: Σ] => R[ClassFunction[x, y], x, y]]]] = {
      new ∃~~>[[ClassFunction[_ <: Σ, _ <: Σ] <: Σ] => ∀[[x <: Σ] => ∀[[y <: Σ] => R[ClassFunction[x, y], x, y]]]] {
        type F[x <: Σ, y <: Σ] = ∃[[z <: Σ] => R[z, x, y]]#S
        val value: ∀[[x <: Σ] => ∀[[y <: Σ] => R[F[x, y], x, y]]] = {
          byContradiction { assumption: ∃[[x <: Σ] => ￢[∀[[y <: Σ] => R[F[x, y], x, y]]]] =>
            type X = assumption.S
            val ev1: ∃[[y <: Σ] => ￢[R[F[X, y], X, y]]] = assumption.value
            type Y = ev1.S
            val ev2: ￢[R[F[X, Y], X, Y]] = ev1.value

            val ev3: ∃[[z <: Σ] => R[z, X, Y]] = forType[Y].instantiate[[y <: Σ] => ∃[[z <: Σ] => R[z, X, y]]](
              forType[X].instantiate[[x <: Σ] => ∀[[y <: Σ] => ∃[[z <: Σ] => R[z, x, y]]]](exists)
            )
            type Z = ev3.S
            val ev4: R[Z, X, Y] = ev3.value
            // since the subtype of F[X, Y] is unique to Z, they are isomorphic.
            // it is therefore safe to cast from G[Z] to G[F[X, Y]] for any G[_].
            // let G[x] = R[x, X, Y], then this cast is safe.
            val ev5: R[F[X, Y], X, Y] = ev4.asInstanceOf[R[F[X, Y], X, Y]]

            ev5 ∧ ev2
          }
        }
      }
  }
  
}

class ComprehensionConstruct(implicit axiom: ZFAxiom) {

/*
  type Comprehension[X, F[_ <: Σ]] <: Σ
  def constraint[X <: Σ, F[_ <: Σ], x <: Σ]: (x ∈ Comprehension[X, F]) <=> ((x ∈ X) ∧ F[x]) = ???
*/

}

class EmptySetConstruct(implicit axiom: ZFAxiom) {
  import Lemma._

  /**
    * There exists an empty set.
    */
  val existence: ∃[isEmpty] = {
    val set = existence

    type Set = set.S

    val emptyExistence: ∃[[y <: Σ] => ∀[[u <: Σ] => (u ∈ y) <=> ((u ∈ Set) ∧ Nothing)]] = separate[Set, [_] => Nothing]

    type EmptySet = emptyExistence.S
    val ev1: ∀[[u <: Σ] => (u ∈ EmptySet) <=> ((u ∈ Set) ∧ Nothing)] = emptyExistence.value
    val ev2: ∀[[u <: Σ] => (u ∈ EmptySet) => Nothing] = byContradiction { assumption: ∃[[u <: Σ] => ￢[u ∈ EmptySet] => Nothing] =>
      type U = assumption.S
      val ev21 = assumption.value
      val ev22 = forType[U].instantiate[[u <: Σ] => (u ∈ EmptySet) <=> ((u ∈ Set) ∧ Nothing)](ev1)
      val ev23 = ev22.implies.andThen { conclusion: (U ∈ Set) ∧ Nothing => conclusion._2 }
      ev21(ev23)
    }
    val ev3: ∀[[u <: Σ] => u ∉ EmptySet] = ev2
  
    forType[EmptySet].generalize[[x <: Σ] => ∀[[y <: Σ] => y ∉ x]](ev3)
  }

  type ∅ = existence.S
  val constraint: isEmpty[∅] = existence.value

  val uniqueness: ∀[[x <: Σ] => isEmpty[x] => (x =::= ∅)] = {
    byContradiction { assumption: ∃[[x <: Σ] => ￢[isEmpty[x] => (x =::= ∅)]] =>
      type X = assumption.S
      val ev1: ￢[isEmpty[X] => (X =::= ∅)] = assumption.value
      val ev2: ∀[[z <: Σ] => (z ∈ X) <=> (z ∈ ∅)] => (X =::= ∅) =
        forType[∅].instantiate[[y <: Σ] => ∀[[z <: Σ] => (z ∈ X) <=> (z ∈ y)] => (X =::= y)](
          forType[X].instantiate[[x <: Σ] => ∀[[y <: Σ] => ∀[[z <: Σ] => (z ∈ x) <=> (z ∈ y)] => (x =::= y)]](extensionality)
        )
      val ev3: isEmpty[X] => ∀[[z <: Σ] => (z ∈ X) <=> (z ∈ ∅)] = { xIsEmpty: ∀[[y <: Σ] => y ∉ X] =>
        byContradiction { assumption3: ∃[[z <: Σ] => ￢[(z ∈ X) <=> (z ∈ ∅)]] =>
          type Z = assumption3.S
          val ev31: ￢[(Z ∈ X) <=> (Z ∈ ∅)] = assumption3.value
          val ev32: (Z ∈ X) => (Z ∈ ∅) = { assumption32: Z ∈ X =>
            assumption32 ∧ forType[Z].instantiate[[y <: Σ] => y ∉ X](xIsEmpty)
          }
          val ev33: (Z ∈ ∅) => (Z ∈ X) = { assumption33: Z ∈ ∅ =>
            assumption33 ∧ forType[Z].instantiate[[y <: Σ] => y ∉ ∅](existence.value)
          }
          val ev34: (Z ∈ X) <=> (Z ∈ ∅) = ev32 ∧ ev33
          ev34 ∧ ev31
        }
      }
      val ev4: isEmpty[X] => (X =::= ∅) = ev3.andThen(ev2)
      ev4 ∧ ev1
    }
  }
}

class PairSetConstruct(implicit axiom: ZFAxiom) {
  import Lemma._
  import Lemma.Predicate._

  val existence: ∀[[x <: Σ] => ∀[[y <: Σ] => ∃[[z <: Σ] => containsTwo[z, x, y]]]] = {
    byContradiction { assumption: ∃[[x <: Σ] => ￢[∀[[y <: Σ] => ∃[[z <: Σ] => containsTwo[z, x, y]]]]] =>
      type X = assumption.S
      val ev1: ∃[[y <: Σ] => ￢[∃[[z <: Σ] => containsTwo[z, X, y]]]] = assumption.value
      type Y = ev1.S
      val ev2: ￢[∃[[z <: Σ] => containsTwo[z, X, Y]]] = ev1.value
      val ev3: ∃[[z <: Σ] => ∀[[w <: Σ] => ((w =::= X) ∨ (w =::= Y)) => (w ∈ z)]] =
        forType[Y].instantiate[[b <: Σ] => ∃[[x <: Σ] => ∀[[w <: Σ] => ((w =::= X) ∨ (w =::= b)) => (w ∈ x)]]](
          forType[X].instantiate[[a <: Σ] => ∀[[b <: Σ] => ∃[[x <: Σ] => ∀[[w <: Σ] => ((w =::= a) ∨ (w =::= b)) => (w ∈ x)]]]](pairing)
        )
      val ev4: ∃[[z <: Σ] => containsTwo[z, X, Y]] = comprehendsExactly[[w <: Σ] => ((w =::= X) ∨ (w =::= Y))](ev3)
      ev4 ∧ ev2
    }
  }

  val uniqueness: ∀[[z <: Σ] => ∀[[w <: Σ] => ∀[[x <: Σ] => ∀[[y <: Σ] => (containsTwo[z, x, y] ∧ containsTwo[w, x, y]) => z =::= w]]]] = {
    byContradiction { assumption: ∃[[z <: Σ] => ￢[∀[[w <: Σ] => ∀[[x <: Σ] => ∀[[y <: Σ] => (containsTwo[z, x, y] ∧ containsTwo[w, x, y]) => z =::= w]]]]] =>
      type Z = assumption.S
      val ev1: ∃[[w <: Σ] => ￢[∀[[x <: Σ] => ∀[[y <: Σ] => (containsTwo[Z, x, y] ∧ containsTwo[w, x, y]) => Z =::= w]]]] = assumption.value
      type W = ev1.S
      val ev2: ∃[[x <: Σ] => ￢[∀[[y <: Σ] => (containsTwo[Z, x, y] ∧ containsTwo[W, x, y]) => Z =::= W]]] = ev1.value
      type X = ev2.S
      val ev3: ∃[[y <: Σ] => ￢[(containsTwo[Z, X, y] ∧ containsTwo[W, X, y]) => Z =::= W]] = ev2.value
      type Y = ev3.S
      val ev4: ￢[(containsTwo[Z, X, Y] ∧ containsTwo[W, X, Y]) => Z =::= W] = ev3.value
      val ev5: (containsTwo[Z, X, Y] ∧ containsTwo[W, X, Y]) => Z =::= W = equivalence[Z, W, [z <: Σ] => (z =::= X) ∨ (z =::= Y)]
      ev5 ∧ ev4
    }
  }

  val pairFunctionExistence: ∃~~>[[++:[_ <: Σ, _ <: Σ] <: Σ] => ∀[[x <: Σ] => ∀[[y <: Σ] => containsTwo[x ++: y, x, y]]]] = {
    createBinaryClassFunction[containsTwo](existence, uniqueness)
  }

  type ++:[x <: Σ, y <: Σ] = pairFunctionExistence.F[x, y]
  val constraint: ∀[[x <: Σ] => ∀[[y <: Σ] => containsTwo[x ++: y, x, y]]] = pairFunctionExistence.value

}

class UnionSetConstruct(implicit axiom: ZFAxiom) {
  import Lemma._
  import Lemma.Predicate._

  val existence: ∀[[x <: Σ] => ∃[[y <: Σ] => y isUnionOf x]] = {
    byContradiction { assumption: ∃[[x <: Σ] => ￢[∃[[y <: Σ] => y isUnionOf x]]] =>
      type F = assumption.S 
      val ev1: ￢[∃[[u <: Σ] => u isUnionOf F]] = assumption.value
      val ev2: ∃[[u <: Σ] => ∀[[y <: Σ] => ∀[[x <: Σ] => ((x ∈ y) ∧ (y ∈ F)) => x ∈ u]]] = {
        forType[F].instantiate[[F <: Σ] => ∃[[u <: Σ] => ∀[[y <: Σ] => ∀[[x <: Σ] => ((x ∈ y) ∧ (y ∈ F)) => x ∈ u]]]](union)
      }
      type U = ev2.S
      val ev3: ∀[[y <: Σ] => ∀[[x <: Σ] => ((x ∈ y) ∧ (y ∈ F)) => x ∈ U]] = ev2.value
      val ev4: ∃[[u <: Σ] => ∀[[x <: Σ] => (x ∈ u) <=> ∃[[Y <: Σ] => ((x ∈ Y) ∧ (Y ∈ F))]]] = {
        val ev41: ∃[[v <: Σ] => ∀[[x <: Σ] => (x ∈ v) <=> (x ∈ U) ∧ ∃[[y <: Σ] => ((x ∈ y) ∧ (y ∈ F))]]] = {
          separate[U, [x <: Σ] => ∃[[y <: Σ] => ((x ∈ y) ∧ (y ∈ F))]]
        }
        type V = ev41.S
        val ev42: ∀[[x <: Σ] => (x ∈ V) <=> ((x ∈ U) ∧ ∃[[y <: Σ] => ((x ∈ y) ∧ (y ∈ F))])] = ev41.value
        val ev43: ∀[[x <: Σ] => (x ∈ V) <=> ∃[[Y <: Σ] => ((x ∈ Y) ∧ (Y ∈ F))]] = {
          val ev431: ∀[[x <: Σ] => ((x ∈ U) ∧ ∃[[y <: Σ] => ((x ∈ y) ∧ (y ∈ F))]) <=> ∃[[Y <: Σ] => ((x ∈ Y) ∧ (Y ∈ F))]] = byContradiction { assumption431 =>
            type X = assumption431.S
            val ev4311: ￢[((X ∈ U) ∧ ∃[[y <: Σ] => ((X ∈ y) ∧ (y ∈ F))]) <=> ∃[[Y <: Σ] => ((X ∈ Y) ∧ (Y ∈ F))]] = assumption431.value
            val implies: ((X ∈ U) ∧ ∃[[y <: Σ] => ((X ∈ y) ∧ (y ∈ F))]) => ∃[[Y <: Σ] => ((X ∈ Y) ∧ (Y ∈ F))] = { _._2 }
            val impliedBy: ∃[[Y <: Σ] => ((X ∈ Y) ∧ (Y ∈ F))] => ((X ∈ U) ∧ ∃[[y <: Σ] => ((X ∈ y) ∧ (y ∈ F))]) = { ex =>
              type Y = ex.S
              val ev4321: (X ∈ Y) ∧ (Y ∈ F) = ex.value
              val ev4322: ((X ∈ Y) ∧ (Y ∈ F)) => X ∈ U = {
                forType[X].instantiate[[x <: Σ] => ((x ∈ Y) ∧ (Y ∈ F)) => x ∈ U](
                  forType[Y].instantiate[[y <: Σ] => ∀[[x <: Σ] => ((x ∈ y) ∧ (y ∈ F)) => x ∈ U]](ev3)
                )
              }
              val ev4323: X ∈ U = ev4322(ev4321)
              ev4323 ∧ ex
            }
            val ev4312: ((X ∈ U) ∧ ∃[[y <: Σ] => ((X ∈ y) ∧ (y ∈ F))]) <=> ∃[[Y <: Σ] => ((X ∈ Y) ∧ (Y ∈ F))] = implies ∧ impliedBy
            ev4312 ∧ ev4311
          }
          forallEquivTransitive[[x <: Σ] => x ∈ V, [x <: Σ] => (x ∈ U) ∧ ∃[[y <: Σ] => ((x ∈ y) ∧ (y ∈ F))], [x <: Σ] => ∃[[Y <: Σ] => ((x ∈ Y) ∧ (Y ∈ F))]](ev42, ev431)
        }
        genExist[[u <: Σ] => ∀[[x <: Σ] => (x ∈ u) <=> ∃[[Y <: Σ] => ((x ∈ Y) ∧ (Y ∈ F))]], V](ev43)
      }
      val ev5: ∃[[u <: Σ] => u isUnionOf F] = ev4
      ev5 ∧ ev1
    }
  }

  val uniqueness: ∀[[z <: Σ] => ∀[[x <: Σ] => ∀[[y <: Σ] => (x isUnionOf z) ∧ (y isUnionOf z) => x =::= y]]] = {
    byContradiction { assumption: ∃[[z <: Σ] => ￢[∀[[x <: Σ] => ∀[[y <: Σ] => (x isUnionOf z) ∧ (y isUnionOf z) => x =::= y]]]] =>
      type Z = assumption.S
      val ev1: ∃[[x <: Σ] => ￢[∀[[y <: Σ] => (x isUnionOf Z) ∧ (y isUnionOf Z) => x =::= y]]] = assumption.value
      type X = ev1.S
      val ev2: ∃[[y <: Σ] => ￢[(X isUnionOf Z) ∧ (y isUnionOf Z) => X =::= y]] = ev1.value
      type Y = ev2.S
      val ev3: ￢[(X isUnionOf Z) ∧ (Y isUnionOf Z) => X =::= Y] = ev2.value
      val ev4: (X isUnionOf Z) ∧ (Y isUnionOf Z) => X =::= Y = equivalence[X, Y, [x <: Σ] => ∃[[Y <: Σ] => ((x ∈ Y) ∧ (Y ∈ Z))]]
      ev4 ∧ ev3
    }
  }

  val unionFunctionExistence: ∃~>[[Union[_ <: Σ] <: Σ] => ∀[[x <: Σ] => Union[x] isUnionOf x]] = createUnaryClassFunction[isUnionOf](existence, uniqueness)

  type Union[x <: Σ] = unionFunctionExistence.F[x]
  val constraint: ∀[[x <: Σ] => Union[x] isUnionOf x] = unionFunctionExistence.value

}

class PowerSetConstruct(implicit axiom: ZFAxiom) {
  import Lemma._
  import Lemma.Predicate._

  val existence: ∀[[x <: Σ] => ∃[[y <: Σ] => y isPowerOf x]] = {
    byContradiction { assumption: ∃[[x <: Σ] => ￢[∃[[y <: Σ] => y isPowerOf x]]] =>
      type X = assumption.S
      val ev1: ￢[∃[[y <: Σ] => y isPowerOf X]] = assumption.value
      val ev2: ∃[[y <: Σ] => ∀[[z <: Σ] => (z ⊂ X) => (z ∈ y)]] = forType[X].instantiate[[x <: Σ] => ∃[[p <: Σ] => ∀[[z <: Σ] => (z ⊂ x) => (z ∈ p)]]](power)
      val ev3: ∃[[y <: Σ] => ∀[[z <: Σ] => (z ∈ y) <=> (z ⊂ X)]] = comprehendsExactly[[z <: Σ] => z ⊂ X](ev2)
      val ev4: ∃[[y <: Σ] => y isPowerOf X] = ev3
      ev4 ∧ ev1
    }
  }

  val uniqueness: ∀[[z <: Σ] => ∀[[x <: Σ] => ∀[[y <: Σ] => (x isPowerOf z) ∧ (y isPowerOf z) => x =::= y]]] = {
    byContradiction { assumption: ∃[[z <: Σ] => ￢[∀[[x <: Σ] => ∀[[y <: Σ] => (x isPowerOf z) ∧ (y isPowerOf z) => x =::= y]]]] =>
      type Z = assumption.S
      val ev1: ￢[∀[[x <: Σ] => ∀[[y <: Σ] => (x isPowerOf Z) ∧ (y isPowerOf Z) => x =::= y]]] = assumption.value
      val ev2: ∃[[x <: Σ] => ￢[∀[[y <: Σ] => (x isPowerOf Z) ∧ (y isPowerOf Z) => x =::= y]]] = ev1
      type X = ev2.S
      val ev3: ∃[[y <: Σ] => ￢[(X isPowerOf Z) ∧ (y isPowerOf Z) => X =::= y]] = ev2.value
      type Y = ev3.S
      val ev4: ￢[(X isPowerOf Z) ∧ (Y isPowerOf Z) => X =::= Y] = ev3.value
      val ev5: (X isPowerOf Z) ∧ (Y isPowerOf Z) => X =::= Y = equivalence[X, Y, [z <: Σ] => z ⊂ Z]
      ev5 ∧ ev4
    }
  }

  val powerFunctionExistence: ∃~>[[Pow[_ <: Σ] <: Σ] => ∀[[x <: Σ] => Pow[x] isPowerOf x]] = createUnaryClassFunction[isPowerOf](existence, uniqueness)

  type Pow[x <: Σ] = powerFunctionExistence.F[x]
  val constraint: ∀[[x <: Σ] => Pow[x] isPowerOf x] = powerFunctionExistence.value
}

class SingletonConstruct(val pairSet: PairSetConstruct) {

  type ++: = pairSet.++:

  type Just[x <: Σ] = x ++: x
  val constraint: ∀[[x <: Σ] => Just[x] isSingletonOf x] = byContradiction { assumption: ∃[[x <: Σ] => ￢[Just[x] isSingletonOf x]] =>
    type X = assumption.S
    val ev1: ￢[Just[X] isSingletonOf X] = assumption.value
    val ev2: containsTwo[Just[X], X, X] = forType[X].instantiate[[y <: Σ] => containsTwo[X ++: y, X, y]](
      forType[X].instantiate[[x <: Σ] => ∀[[y <: Σ] => containsTwo[x ++: y, x, y]]](pairSet.constraint)
    )
    val ev3: ∀[[w <: Σ] => (w ∈ Just[X]) <=> ((w =::= X) ∨ (w =::= X))] = ev2
    val ev4: ∀[[w <: Σ] => (w ∈ Just[X]) <=> (w =::= X)] = byContradiction { assumption4: ∃[[w <: Σ] => ￢[(w ∈ Just[X]) <=> (w =::= X)]] =>
      type W = assumption4.S
      val ev41: ￢[(W ∈ Just[X]) <=> (W =::= X)] = assumption4.value
      val ev42: (W ∈ Just[X]) <=> ((W =::= X) ∨ (W =::= X)) = forType[W].instantiate[[w <: Σ] => (w ∈ Just[X]) <=> ((w =::= X) ∨ (w =::= X))](ev3)
      val ev43: ((W =::= X) ∨ (W =::= X)) <=> (W =::= X) = {
        val implies = { from: (W =::= X) ∨ (W =::= X) => removeDisj(from)(identity)(identity) }
        val impliedBy: ((W =::= X) ∨ (W =::= X)) <= (W =::= X) = Left.apply
        implies ∧ impliedBy
      }
      val ev44: (W ∈ Just[X]) <=> (W =::= X) = ev42.andThen(ev43)
      ev44 ∧ ev41
    }
    ev4 ∧ ev1
  }

}

class BinaryUnionConstruct(val pairSet: PairSetConstruct,
                           val unionSet: UnionSetConstruct) {

  type Union = unionSet.Union
  type ++: = pairSet.++:

  type ∪[x <: Σ, y <: Σ] = Union[x ++: y]
  val constraintValue: ∀[[x <: Σ] => ∀[[y <: Σ] => isSumOf[x ∪ y, x, y]]] = ???

  def constraint[x <: Σ, y <: Σ]: isSumOf[x ∪ y, x, y] = {
    forType[y].instantiate[[y1 <: Σ] => isSumOf[x ∪ y1, x, y1]](
      forType[x].instantiate[[x1 <: Σ] => ∀[[y1 <: Σ] => isSumOf[x1 ∪ y1, x1, y1]]](
        constraintValue
      )
    )
  }

}

class IntersectionConstruct(val union: UnionSetConstruct) {
  
  // TODO
  type Intersection[F <: Σ] = union.Union[F]
  val constraintVal: ∀[[F <: Σ] => ∀[[z <: Σ] => (z ∈ Intersection[F]) <=> (F hasAll ([x <: Σ] => z ∈ x))]] = ???

  def constraint[F <: Σ, z <: Σ]: (z ∈ Intersection[F]) <=> (F hasAll ([x <: Σ] => z ∈ x)) = {
    forType[z].instantiate[[z1 <: Σ] => (z1 ∈ Intersection[F]) <=> (F hasAll ([x <: Σ] => z1 ∈ x))](
      forType[F].instantiate[[F1 <: Σ] => ∀[[z1 <: Σ] => (z1 ∈ Intersection[F1]) <=> (F1 hasAll ([x <: Σ] => z1 ∈ x))]](
        constraintVal
      )
    )
  }

}

class BinaryIntersectionConstruct(val pairSet: PairSetConstruct,
                                  val intersection: IntersectionConstruct) {

  type Intersection = intersection.Intersection
  type ++: = pairSet.++:

  type ∩[x <: Σ, y <: Σ] = Intersection[x ++: y]
  val constraintValue: ∀[[x <: Σ] => ∀[[y <: Σ] => isIntersectionOf[x ∩ y, x, y]]] = ???

  def constraint[x <: Σ, y <: Σ]: isIntersectionOf[x ∩ y, x, y] = {
    forType[y].instantiate[[y1 <: Σ] => isIntersectionOf[x ∩ y1, x, y1]](
      forType[x].instantiate[[x1 <: Σ] => ∀[[y1 <: Σ] => isIntersectionOf[x1 ∩ y1, x1, y1]]](constraintValue)
    )
  }

}

class OrderedPairConstruct(val pairSet: PairSetConstruct, val singleton: SingletonConstruct) {

  type ++:[a <: Σ, b <: Σ] = pairSet.++:[a, b]
  type Just[a <: Σ] = singleton.Just[a]

  type :::[a <: Σ, b <: Σ] = Just[a] ++: Just[a ++: b]
  val constraintValue: ∀[[a <: Σ] => ∀[[b <: Σ] => ∀[[c <: Σ] => ∀[[d <: Σ] => ((a ::: b) =::= (c ::: d)) <=> ((a =::= c) ∧ (b =::= d))]]]] = ???

  def constraint[a <: Σ, b <: Σ, c <: Σ, d <: Σ]: ((a ::: b) =::= (c ::: d)) <=> ((a =::= c) ∧ (b =::= d)) = {
    forType[d].instantiate[[d1 <: Σ] => ((a ::: b) =::= (c ::: d1)) <=> ((a =::= c) ∧ (b =::= d1))](
      forType[c].instantiate[[c1 <: Σ] => ∀[[d1 <: Σ] => ((a ::: b) =::= (c1 ::: d1)) <=> ((a =::= c1) ∧ (b =::= d1))]](
        forType[b].instantiate[[b1 <: Σ] => ∀[[c1 <: Σ] => ∀[[d1 <: Σ] => ((a ::: b1) =::= (c1 ::: d1)) <=> ((a =::= c1) ∧ (b1 =::= d1))]]](
          forType[a].instantiate[[a1 <: Σ] => ∀[[b1 <: Σ] => ∀[[c1 <: Σ] => ∀[[d1 <: Σ] => ((a1 ::: b1) =::= (c1 ::: d1)) <=> ((a1 =::= c1) ∧ (b1 =::= d1))]]]](
            constraintValue
          )
        )
      )
    )
  }

}

class BasicConstructs(implicit axiom: ZFAxiom) {
  import Lemma._

  val emptySet = new EmptySetConstruct
  type ∅ = emptySet.∅

  val pairSet = new PairSetConstruct
  type ++:[x <: Σ, y <: Σ] = pairSet.++:[x, y]

  val unionSet = new UnionSetConstruct
  type Union[F <: Σ] = unionSet.Union[F]

  val powerSet = new PowerSetConstruct
  type Pow[x <: Σ] = powerSet.Pow[x]

  val singleton = new SingletonConstruct(pairSet)
  type Just[x <: Σ] = singleton.Just[x]

  val binaryUnion = new BinaryUnionConstruct(pairSet, unionSet)
  type ∪[x <: Σ, y <: Σ] = binaryUnion.∪[x, y]

  val intersection = new IntersectionConstruct(unionSet)
  type Intersection[F <: Σ] = intersection.Intersection[F]

  val binaryIntersection = new BinaryIntersectionConstruct(pairSet, intersection)
  type ∩[x <: Σ, y <: Σ] = binaryIntersection.∩[x, y]

  val orderedPair = new OrderedPairConstruct(pairSet, singleton)
  type :::[a <: Σ, b <: Σ] = orderedPair.:::[a, b]

}

class ElementaryTheorems(implicit axiom: ZFAxiom) {

  /**
   * There is no set of all sets.
   */
  val noSetOfAllSets: ￢[∃[[x <: Σ] => ∀[[y <: Σ] => y ∈ x]]] = {
    def lemma1[A, B]: ￢[(A <=> (B ∧ ￢[A])) ∧ B] = byContradiction { assumption: (A <=> (B ∧ ￢[A])) ∧ B =>
      val (aEqBAndNotA, b) = assumption
      def ev1: ￢[A] => A = { notA: ￢[A] => aEqBAndNotA.impliedBy(b ∧ notA) }
      def ev2: A => ￢[A] = { a: A => aEqBAndNotA.implies(a)._2 }
      val notAEqNotA = byContradiction { aEqNotA: A <=> ￢[A] =>
        val notA = byContradiction { a: A => a ∧ aEqNotA.implies(a) }
        val a: A = aEqNotA.impliedBy(notA)
        a ∧ notA
      }
      notAEqNotA(ev2 ∧ ev1)
    }
  
    byContradiction { assumption: ∃[[x <: Σ] => ∀[[y <: Σ] => y ∈ x]] =>
      import Lemma._

      type S = assumption.S
      val setOfAllSets = assumption.value

      val paradoxicalExistence: ∃[[z <: Σ] => ∀[[u <: Σ] => (u ∈ z) <=> ((u ∈ S) ∧ (u ∉ u))]] = separate[S, [X <: Σ] => X ∉ X]
      type Z = paradoxicalExistence.S
      val paradoxicalSet: ∀[[u <: Σ] => (u ∈ Z) <=> ((u ∈ S) ∧ (u ∉ u))] = paradoxicalExistence.value
      val ev1: (Z ∈ Z) <=> ((Z ∈ S) ∧ (Z ∉ Z)) = forType[Z].instantiate[[u <: Σ] => (u ∈ Z) <=> ((u ∈ S) ∧ (u ∉ u))](paradoxicalSet)
      val ev2: Z ∈ S = forType[Z].instantiate[[y <: Σ] => y ∈ S](setOfAllSets)
      lemma1(ev1 ∧ ev2)
    }
  }

}
