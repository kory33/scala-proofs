package com.github.kory33.proof.set

import com.github.kory33.proof.logic.predicate.PredicateLogicDefinitions.{∃, _}
import com.github.kory33.proof.logic.propositional.LogicDefinitions._
import com.github.kory33.proof.set.SetDefinitions.{∈, _}

trait ZFAxiom {

  /**
    * Axiom of existence.
    *
    * There exists a set.
    */
  def existence: ∃[({ type λ[x] =
    x =#= x
  })#λ]

  /**
    * Axiom of extensionality.
    *
    * For all set x and y, x contains and is contained in y when they have exactly same elements.
    */
  def extensionality:
    ∀[({ type λ1[x] =
      ∀[({ type λ2[y] =
        ∀[({ type λ3[z] = (z ∈ x) ≣ (z ∈ y) })#λ3] => x =#= y
      })#λ2]
    })#λ1]

  /**
    * Schema of separation.
    *
    * For every binary predicate F of free variables,
    * every set x and parameter p, there exists set y = { u ∈ x | F(u, p) }.
    *
    * @tparam F binary predicate
    */
  def separation[F[_, _]]:
    ∀[({ type λ1[x] =
      ∀[({ type λ2[p] =
        ∃[({ type λ3[y] =
          ∀[({ type λ4[u] = (u ∈ y) ≣ ((u ∈ x) ∧ F[u, p])
          })#λ4]
        })#λ3]
      })#λ2]
    })#λ1]

  /**
    * Axiom of pairing
    *
    * For any a and b there exists x that contains a and b.
    */
  def pairing:
    ∀[({ type λ1[a] =
      ∀[({ type λ2[b] =
        ∃[({ type λ3[x] =
          (a ∈ x) ∧ (a ∈ x)
        })#λ3]
      })#λ2]
    })#λ1]

  /**
    * Axiom of union.
    *
    * For every family F there exists a set U containing all elements of F.
    */
  def union[F <: Family]:
    ∃[({ type λ1[U] =
      ∀[({ type λ2[Y] =
        ∀[({ type λ3[x] =
          ((x ∈ Y) ∧ (Y ∈ F)) => x ∈ U
        })#λ3]
      })#λ2]
    })#λ1]

  /**
    * Axiom of power set.
    *
    * For every set x there exists a set P containing all subsets of x.
    */
  def power:
    ∀[({ type λ1[X] =
      ∃[({ type λ2[P] =
        ∀[({ type λ3[z] =
          (z ⊂ X) => (z ∈ P)
        })#λ3]
      })#λ2]
    })#λ1]

  /**
    * Axiom of empty set.
    *
    * There exists an empty set.
    *
    * This is actually not in axiom set and is deduced from other axioms
    */
  def empty:
    ∃[({ type λ1[x] =
      ∀[({ type λ2[y] =
        y ∈ x => y =/= y
      })#λ2]
    })#λ1] // TODO prove.
}
