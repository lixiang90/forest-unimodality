import ForestUnimodality.ForestLeaf
import ForestUnimodality.GraphBounds
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! The initial forest growth inequality follows from leaf deletion and two
strictly smaller induced forests. Subtraction is over the reals, so the
statement also covers degrees where n-3k is negative. -/

namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

theorem countIndependent_le_of_one_extra_vertex (G : SimpleGraph V)
    {C H : Finset V} (hCH : C ⊆ H) (hdiff : (H \ C).card ≤ 1) (k : ℕ) :
    countIndependent G H (k + 1) ≤ countIndependent G C (k + 1) + countIndependent G C k := by
  classical
  by_cases hempty : H \ C = ∅
  · have hHC := sdiff_eq_empty_iff_subset.mp hempty
    have heq : H = C := subset_antisymm hHC hCH
    rw [heq]
    omega
  · have hcard : (H \ C).card = 1 := by
      have hp := card_pos.mpr (nonempty_iff_ne_empty.mpr hempty)
      omega
    obtain ⟨u, hu⟩ := card_eq_one.mp hcard
    have humem : u ∈ H \ C := by rw [hu]; simp
    obtain ⟨huH, huC⟩ := mem_sdiff.mp humem
    have herase : H.erase u = C := by
      ext x
      constructor
      · intro hx
        by_contra hxC
        have hxD : x ∈ H \ C := mem_sdiff.mpr ⟨(mem_erase.mp hx).2, hxC⟩
        have hxu : x = u := by simpa [hu] using hxD
        exact (mem_erase.mp hx).1 hxu
      · intro hx
        exact mem_erase.mpr ⟨fun h => huC (h ▸ hx), hCH hx⟩
    have hclosed : H \ closedNeighborhoodIn G H u ⊆ C := by
      rw [← herase]
      intro x hx
      obtain ⟨hxH, hxu, _⟩ := mem_sdiff_closedNeighborhoodIn.mp hx
      exact mem_erase.mpr ⟨hxu, hxH⟩
    rw [countIndependent_succ_delete_vertex G H huH k, herase]
    exact Nat.add_le_add_left (countIndependent_mono G hclosed k) _

theorem countIndependent_initial_growth (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) (k : ℕ) :
    ((S.card : ℝ) - 3 * (k : ℝ)) * (countIndependent G S k : ℝ) ≤
      ((k : ℝ) + 1) * (countIndependent G S (k + 1) : ℝ) := by
  classical
  revert k
  refine S.strongInductionOn ?_
  intro S ih k
  cases k with
  | zero => simp
  | succ k =>
    by_cases hzero : S.card = 0
    · simp only [hzero, Nat.cast_zero, zero_sub, Nat.cast_add,
        Nat.cast_one]
      have hc : 0 ≤ (countIndependent G S (k + 1) : ℝ) := Nat.cast_nonneg _
      have hd : 0 ≤ (countIndependent G S (k + 1 + 1) : ℝ) := Nat.cast_nonneg _
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have hS : S.Nonempty := card_pos.mp (by omega)
    obtain ⟨v, hv, hsmall⟩ := exists_closedNeighborhoodIn_card_le_two G hG S hS
    have hclosed : closedNeighborhoodIn G S v ⊆ S := by
      unfold closedNeighborhoodIn
      exact filter_subset _ _
    have hvclosed : v ∈ closedNeighborhoodIn G S v := by
      simp [closedNeighborhoodIn, hv]
    have hCH : S \ closedNeighborhoodIn G S v ⊆ S.erase v := by
      intro x hx
      obtain ⟨hxS, hxv, _⟩ := mem_sdiff_closedNeighborhoodIn.mp hx
      exact mem_erase.mpr ⟨hxv, hxS⟩
    have hH := card_erase_add_one hv
    have hC := card_sdiff_add_card_eq_card hclosed
    have hdiff : (S.erase v \ (S \ closedNeighborhoodIn G S v)).card ≤ 1 := by
      rw [card_sdiff_of_subset hCH]
      omega
    have hcompare := countIndependent_le_of_one_extra_vertex G hCH hdiff k
    have hh := ih (S.erase v) (erase_ssubset hv) (k + 1)
    have hc := ih (S \ closedNeighborhoodIn G S v)
      (sdiff_ssubset hclosed ⟨v, hvclosed⟩) k
    have hHr : ((S.erase v).card : ℝ) + 1 = (S.card : ℝ) := by exact_mod_cast hH
    have hCr : (S.card : ℝ) ≤ ((S \ closedNeighborhoodIn G S v).card : ℝ) + 2 := by
      exact_mod_cast (show S.card ≤ (S \ closedNeighborhoodIn G S v).card + 2 by omega)
    have hcompareR : (countIndependent G (S.erase v) (k + 1) : ℝ) ≤
        (countIndependent G (S \ closedNeighborhoodIn G S v) (k + 1) : ℝ) +
        (countIndependent G (S \ closedNeighborhoodIn G S v) k : ℝ) := by
      exact_mod_cast hcompare
    have hsizeW := mul_le_mul_of_nonneg_right hCr
      (Nat.cast_nonneg (α := ℝ) (countIndependent G (S \ closedNeighborhoodIn G S v) k))
    rw [countIndependent_succ_delete_vertex G S hv k,
      countIndependent_succ_delete_vertex G S hv (k + 1)]
    simp only [Nat.cast_add, Nat.cast_one] at hh ⊢
    nlinarith

/-- Every pre-quarter step is nondecreasing. The cutoff is ceil(n/4). -/
theorem countIndependent_le_succ_of_quarter (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) (k : ℕ) (hk : k < (S.card + 3) / 4) :
    countIndependent G S k ≤ countIndependent G S (k + 1) := by
  have h := countIndependent_initial_growth G hG S k
  have hn : 4 * k + 1 ≤ S.card := by omega
  have hnr : 4 * (k : ℝ) + 1 ≤ (S.card : ℝ) := by exact_mod_cast hn
  have hkn : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hc : 0 ≤ (countIndependent G S k : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hnr hc
  have hout : (countIndependent G S k : ℝ) ≤ countIndependent G S (k + 1) := by
    nlinarith
  exact_mod_cast hout

#print axioms countIndependent_initial_growth
#print axioms countIndependent_le_succ_of_quarter
end ForestUnimodality
