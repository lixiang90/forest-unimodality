import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Independently written counting vocabulary for the actual graph objects.
Definitions are relative to a finite vertex subset, so deletion arguments do
not change vertex types. No forest or unimodality theorem is assumed here. -/

namespace ForestUnimodality

open Finset

variable {V : Type*} [DecidableEq V]

/-- All independent subsets of a finite vertex set. -/
noncomputable def independentSubsets (G : SimpleGraph V) (S : Finset V) :
    Finset (Finset V) := by
  classical
  exact S.powerset.filter fun J => G.IsIndepSet (J : Set V)

@[simp] theorem mem_independentSubsets {G : SimpleGraph V} {S J : Finset V} :
    J ∈ independentSubsets G S ↔ J ⊆ S ∧ G.IsIndepSet (J : Set V) := by
  classical
  simp [independentSubsets]

/-- The number of independent k-subsets of S. -/
noncomputable def countIndependent (G : SimpleGraph V) (S : Finset V) (k : ℕ) : ℕ :=
  ((independentSubsets G S).filter fun J => J.card = k).card

/-- Independence generating function over an arbitrary coefficient semiring. -/
noncomputable def partitionFunction {R : Type*} [CommSemiring R]
    (G : SimpleGraph V) (S : Finset V) (z : R) : R :=
  ∑ J ∈ independentSubsets G S, z^J.card

/-- Vertices in I which may be added to an independent set J. -/
noncomputable def available (G : SimpleGraph V) (I J : Finset V) : Finset V := by
  classical
  exact I.filter fun v => ∀ w ∈ J, ¬ G.Adj v w

@[simp] theorem mem_available {G : SimpleGraph V} {I J : Finset V} {v : V} :
    v ∈ available G I J ↔ v ∈ I ∧ ∀ w ∈ J, ¬ G.Adj v w := by
  classical
  simp [available]

theorem available_subset (G : SimpleGraph V) (I J : Finset V) :
    available G I J ⊆ I := by
  classical
  exact filter_subset _ _

end ForestUnimodality
