import ForestUnimodality.Concentration
import ForestUnimodality.ReleaseBounds
import Mathlib.Data.Real.Basic

/-! Exact upper envelopes for the two deletion statistics. The mass
concentration argument is proved for integer release coordinates. -/

namespace ForestUnimodality
open Finset

def releaseUpperEnvelope (r m h L D : ℕ) : ℕ :=
  (D / L) * (m + L - h) +
    if D / L < r then (m + D % L - h) + (r - D / L - 1) * (m - h) else 0

def thresholdUpperEnvelope (r m h L D : ℕ) : ℕ :=
  if h ≤ m then r else if h ≤ m + L then min r (D / (h - m)) else 0

theorem sum_release_excess_le_envelope {V : Type*} (J : Finset V) (p : V → ℕ)
    (r m h L D : ℕ) (hcard : J.card = r) (hL : 0 < L) (hD : D ≤ r * L)
    (hcap : ∀ u ∈ J, p u ≤ L) (hsum : (∑ u ∈ J, p u) ≤ D) :
    (∑ u ∈ J, (m + p u - h)) ≤ releaseUpperEnvelope r m h L D := by
  classical
  have hdiv := Nat.mod_add_div D L
  have hq : D / L ≤ r := by
    have hm := (Nat.div_mul_le_self D L).trans hD
    exact Nat.le_of_mul_le_mul_right hm hL
  have hrem_zero : D / L = r → D % L = 0 := by
    intro heq
    rw [heq, Nat.mul_comm L r] at hdiv
    omega
  by_cases hhm : h ≤ m
  · have hsum' : (∑ u ∈ J, (m + p u - h)) = r * (m - h) + ∑ u ∈ J, p u := by
      calc
        _ = ∑ u ∈ J, ((m - h) + p u) := by
          apply sum_congr rfl
          intro u _
          omega
        _ = _ := by simp [sum_add_distrib, hcard]
    rw [hsum']
    have hLsub : m + L - h = m - h + L := by omega
    have hRsub : m + D % L - h = m - h + D % L := by omega
    unfold releaseUpperEnvelope
    split_ifs with hqr
    · rw [hLsub, hRsub]
      have hrq : r - D / L - 1 + D / L + 1 = r := by omega
      nlinarith
    · have heq : D / L = r := by omega
      have hz := hrem_zero heq
      rw [hLsub, heq, add_zero]
      rw [heq, hz] at hdiv
      nlinarith
  · have hsum' : (∑ u ∈ J, (m + p u - h)) = ∑ u ∈ J, (p u - (h - m)) := by
      apply sum_congr rfl
      intro u _
      omega
    rw [hsum']
    have hb := sum_tsub_le_concentrated J p L D (h - m) hcap hsum
    have hLsub : m + L - h = L - (h - m) := by omega
    have hRsub : m + D % L - h = D % L - (h - m) := by omega
    have hmzero : m - h = 0 := by omega
    unfold releaseUpperEnvelope
    split_ifs with hqr
    · simpa [hLsub, hRsub, hmzero] using hb
    · have heq : D / L = r := by omega
      have hz := hrem_zero heq
      simpa [hLsub, hz] using hb

theorem card_release_threshold_le_envelope {V : Type*} (J : Finset V) (p : V → ℕ)
    (r m h L D : ℕ) (hcard : J.card = r)
    (hcap : ∀ u ∈ J, p u ≤ L) (hsum : (∑ u ∈ J, p u) ≤ D) :
    (J.filter fun u => h ≤ m + p u).card ≤ thresholdUpperEnvelope r m h L D := by
  classical
  unfold thresholdUpperEnvelope
  split_ifs with hhm hhL
  · simpa [hcard] using card_le_card (filter_subset (fun u => h ≤ m + p u) J)
  · apply le_min
    · simpa [hcard] using card_le_card (filter_subset (fun u => h ≤ m + p u) J)
    · have ht : 0 < h - m := by omega
      apply (Nat.le_div_iff_mul_le ht).mpr
      calc
        (J.filter fun u => h ≤ m + p u).card * (h - m) =
            ∑ _u ∈ J.filter (fun u => h ≤ m + p u), (h - m) := by simp
        _ ≤ ∑ u ∈ J.filter (fun u => h ≤ m + p u), p u := by
          apply sum_le_sum
          intro u hu
          have := (mem_filter.mp hu).2
          omega
        _ ≤ ∑ u ∈ J, p u :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; exact Nat.zero_le _)
        _ ≤ D := hsum
  · apply Nat.le_zero.mpr
    apply card_eq_zero.mpr
    apply filter_eq_empty_iff.mpr
    intro u hu hqual
    have hp := hcap u hu
    omega

#print axioms sum_release_excess_le_envelope
#print axioms card_release_threshold_le_envelope
end ForestUnimodality
