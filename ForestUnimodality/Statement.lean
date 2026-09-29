import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Powerset

/-!
Full intended target for JSP-000826 / Erdős 993.

The target concerns every finite forest, including the empty forest,
disconnected forests, and isolated vertices. The `CompleteTarget` proposition
below is a specification, not a proved theorem. In particular, no size threshold
or unproved analytic hypothesis is part of the proposed final statement.
-/

namespace ForestUnimodality

/-- The coefficient of degree k in the independence polynomial. -/
noncomputable def independentCount {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.powerset.filter fun S : Finset (Fin n) =>
    S.card = k ∧ G.IsIndepSet (S : Set (Fin n))).card

/-- Weak unimodality, with a plateau allowed. -/
def WeaklyUnimodal (f : ℕ → ℕ) : Prop :=
  ∃ p : ℕ, (∀ k < p, f k ≤ f (k + 1)) ∧
    (∀ k, p ≤ k → f (k + 1) ≤ f k)

/-- Specification only: a complete proof must inhabit this proposition. -/
def CompleteTarget : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    G.IsAcyclic → WeaklyUnimodal (independentCount G)

/-- Once a sequence has a nonincreasing step, if it never recovers, it is unimodal.
This is the logical assembly used by finite sign certificates. -/
theorem unimodal_of_no_recovery (f : ℕ → ℕ)
    (hex : ∃ k, f (k + 1) ≤ f k)
    (hnext : ∀ k, f (k + 1) ≤ f k → f (k + 2) ≤ f (k + 1)) :
    WeaklyUnimodal f := by
  classical
  refine ⟨Nat.find hex, ?_, ?_⟩
  · intro k hk
    exact le_of_lt (lt_of_not_ge (Nat.find_min hex hk))
  · intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact Nat.find_spec hex
    | succ k hk ih => exact hnext k ih

/-- No graph on n vertices has an independent set larger than n. -/
theorem independentCount_eq_zero_of_gt {n k : ℕ} (G : SimpleGraph (Fin n))
    (hk : n < k) : independentCount G k = 0 := by
  classical
  unfold independentCount
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro S _ hS
  have hcard : S.card ≤ n := by
    simpa using (Finset.card_le_univ S)
  omega

/-- A final graph proof can discharge only the no-recovery property: the
existence of an eventual nonincreasing step follows from finite support. -/
theorem independentCount_unimodal_of_no_recovery {n : ℕ} (G : SimpleGraph (Fin n))
    (hnext : ∀ k, independentCount G (k + 1) ≤ independentCount G k →
      independentCount G (k + 2) ≤ independentCount G (k + 1)) :
    WeaklyUnimodal (independentCount G) := by
  apply unimodal_of_no_recovery _ ?_ hnext
  refine ⟨n + 1, ?_⟩
  rw [independentCount_eq_zero_of_gt G (show n < n + 1 + 1 by omega)]
  exact Nat.zero_le _

#print axioms unimodal_of_no_recovery
#print axioms independentCount_unimodal_of_no_recovery

end ForestUnimodality
