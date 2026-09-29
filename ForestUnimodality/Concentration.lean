import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! An exact integer concentration bound for sums of threshold excesses. -/

namespace ForestUnimodality
open Finset

/-- Capped nonnegative integer masses maximize their total excess above a
threshold by filling whole caps and then one remainder. -/
theorem sum_tsub_le_concentrated {V : Type*} (J : Finset V) (p : V → ℕ)
    (L D t : ℕ) (hcap : ∀ u ∈ J, p u ≤ L) (hsum : (∑ u ∈ J, p u) ≤ D) :
    (∑ u ∈ J, (p u - t)) ≤ (D / L) * (L - t) + (D % L - t) := by
  classical
  by_cases htL : L ≤ t
  · have hz : ∀ u ∈ J, p u - t = 0 := by
      intro u hu
      exact Nat.sub_eq_zero_of_le ((hcap u hu).trans htL)
    simp only [sum_congr rfl hz, sum_const_zero]
    exact Nat.zero_le _
  have htL' : t ≤ L := by omega
  let A := J.filter fun u => t < p u
  have hrestrict : (∑ u ∈ J, (p u - t)) = ∑ u ∈ A, (p u - t) := by
    symm
    apply sum_subset (filter_subset _ _)
    intro u hu hnot
    have hp : p u ≤ t := by
      by_contra hgt
      exact hnot (mem_filter.mpr ⟨hu, by omega⟩)
    exact Nat.sub_eq_zero_of_le hp
  have htotal : (∑ u ∈ A, p u) ≤ D := by
    apply le_trans _ hsum
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; exact Nat.zero_le _)
  have hmass : (∑ u ∈ A, (p u - t)) + A.card * t = ∑ u ∈ A, p u := by
    rw [show A.card * t = ∑ _u ∈ A, t by simp, ← sum_add_distrib]
    apply sum_congr rfl
    intro u hu
    exact Nat.sub_add_cancel (le_of_lt (mem_filter.mp hu).2)
  have hsize : (∑ u ∈ A, (p u - t)) ≤ A.card * (L - t) := by
    calc
      (∑ u ∈ A, (p u - t)) ≤ ∑ _u ∈ A, (L - t) := by
        apply sum_le_sum
        intro u hu
        exact Nat.sub_le_sub_right (hcap u (mem_filter.mp hu).1) t
      _ = _ := by simp
  rw [hrestrict]
  by_cases hcount : A.card ≤ D / L
  · exact hsize.trans ((Nat.mul_le_mul_right (L - t) hcount).trans (Nat.le_add_right _ _))
  · have hcount' : D / L + 1 ≤ A.card := by omega
    have hct := Nat.mul_le_mul_right t hcount'
    have hdiv := Nat.mod_add_div D L
    have hsub := Nat.sub_add_cancel htL'
    by_cases hrem : t ≤ D % L
    · have hrsub := Nat.sub_add_cancel hrem
      nlinarith
    · have hrsub : D % L - t = 0 := Nat.sub_eq_zero_of_le (by omega)
      rw [hrsub, add_zero]
      nlinarith

#print axioms sum_tsub_le_concentrated
end ForestUnimodality
