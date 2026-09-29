import ForestUnimodality.UnitActivityPathDensity
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Rat.Cast.Order

/-! Rational branch inequalities for the uniform hard-core mean bound.
The four kinds are singleton, edge, any three-vertex tree, and a branch
of size at least four.  No exact deletion ratio is needed for size three.
All graph/statistical premises remain explicit in this scalar module. -/
namespace ForestUnimodality.UnitActivityBranchDensity
open Finset

abbrev Kind := Fin 4
def a : ℚ := 276393 / 1000000
def c : ℚ := 144420 / 1000000
def fullExcess : Kind → ℚ
  | ⟨0, _⟩ => 1 / 2 - a
  | ⟨1, _⟩ => 2 / 3 - 2 * a
  | ⟨2, _⟩ => 1 - 3 * a
  | ⟨3, _⟩ => c
def deletedExcess : Kind → ℚ
  | ⟨0, _⟩ => -a
  | ⟨1, _⟩ => 1 / 2 - 2 * a
  | ⟨2, _⟩ => 2 / 3 - 3 * a
  | ⟨3, _⟩ => c - a
def ratioLower : Kind → ℚ
  | ⟨0, _⟩ => 1 / 2
  | ⟨1, _⟩ => 2 / 3
  | ⟨2, _⟩ => 1 / 2
  | ⟨3, _⟩ => 1 / 2
def ratioUpper : Kind → ℚ
  | ⟨0, _⟩ => 1 / 2
  | ⟨1, _⟩ => 2 / 3
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1

theorem ratio_bounds (i : Kind) :
    1 / 2 ≤ ratioLower i ∧ ratioLower i ≤ ratioUpper i ∧ ratioUpper i ≤ 1 := by
  fin_cases i <;> norm_num [ratioLower, ratioUpper]

theorem branch_affine_lower (i : Kind) {r : ℝ}
    (hr : 1 / 2 ≤ r) (hr1 : r ≤ 1) (hleaf : i = 0 → 2 / 3 ≤ r) :
    (219452 / 1000000 : ℝ) * r - 105572 / 1000000 ≤
      r * (fullExcess i : ℝ) + (1 - r) * (deletedExcess i : ℝ) := by
  fin_cases i <;> norm_num [fullExcess, deletedExcess, a, c] at * <;> linarith

theorem high_degree_lower (k : ℕ) (hk : 4 ≤ k) {r : ℝ}
    (hr : 1 / 2 ≤ r) (hr1 : r ≤ 1) :
    (c : ℝ) ≤ 1 - r - (a : ℝ) +
      (k : ℝ) * ((219452 / 1000000 : ℝ) * r - 105572 / 1000000) := by
  have hk' : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hg : 0 ≤ (219452 / 1000000 : ℝ) * r - 105572 / 1000000 := by linarith
  have hm := mul_nonneg (sub_nonneg.mpr hk') hg
  norm_num [a, c]
  nlinarith

def threeValue (i j k : Kind) (r : ℚ) : ℚ :=
  1 - r - a + r * (fullExcess i + fullExcess j + fullExcess k) +
    (1 - r) * (deletedExcess i + deletedExcess j + deletedExcess k)

def threeLower (i j k : Kind) : ℚ :=
  1 / (1 + ratioUpper i * ratioUpper j * ratioUpper k)
def threeUpper (i j k : Kind) : ℚ :=
  1 / (1 + ratioLower i * ratioLower j * ratioLower k)

set_option maxHeartbeats 0 in
theorem three_endpoints : ∀ i j k : Kind,
    c ≤ threeValue i j k (threeLower i j k) ∧
    c ≤ threeValue i j k (threeUpper i j k) := by
  intro i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [threeValue, threeLower, threeUpper, fullExcess, deletedExcess,
      ratioLower, ratioUpper, a, c]

theorem three_lower (i j k : Kind) {r : ℝ}
    (hlo : (threeLower i j k : ℝ) ≤ r)
    (hhi : r ≤ (threeUpper i j k : ℝ)) :
    (c : ℝ) ≤ 1 - r - (a : ℝ) +
      r * ((fullExcess i : ℝ) + fullExcess j + fullExcess k) +
      (1 - r) * ((deletedExcess i : ℝ) + deletedExcess j + deletedExcess k) := by
  have h0 : (c : ℝ) ≤ (threeValue i j k (threeLower i j k) : ℝ) := by
    exact_mod_cast (three_endpoints i j k).1
  have h1 : (c : ℝ) ≤ (threeValue i j k (threeUpper i j k) : ℝ) := by
    exact_mod_cast (three_endpoints i j k).2
  unfold threeValue at h0 h1
  push_cast at h0 h1
  by_cases hs : 0 ≤ (fullExcess i : ℝ) + fullExcess j + fullExcess k -
      deletedExcess i - deletedExcess j - deletedExcess k - 1
  · nlinarith [mul_nonneg hs (sub_nonneg.mpr hlo)]
  · nlinarith [mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hs) (sub_nonpos.mpr hhi)]

#print axioms branch_affine_lower
#print axioms high_degree_lower
#print axioms three_endpoints
#print axioms three_lower

variable {ι : Type*} [DecidableEq ι]

theorem branching_lower (s : Finset ι) (kind : ι → Kind) (R : ι → ℝ)
    (hk : 3 ≤ s.card)
    (hlo : ∀ i ∈ s, (ratioLower (kind i) : ℝ) ≤ R i)
    (hhi : ∀ i ∈ s, R i ≤ (ratioUpper (kind i) : ℝ)) :
    let r := 1 / (1 + ∏ i ∈ s, R i)
    (c : ℝ) ≤ 1 - r - (a : ℝ) +
      ∑ i ∈ s, (r * (fullExcess (kind i) : ℝ) +
        (1 - r) * (deletedExcess (kind i) : ℝ)) := by
  let r : ℝ := 1 / (1 + ∏ i ∈ s, R i)
  have hR0 : ∀ i ∈ s, 0 ≤ R i := by
    intro i hi
    have hl : (1 / 2 : ℝ) ≤ (ratioLower (kind i) : ℝ) := by
      have hh : (((1 / 2 : ℚ) : ℝ)) ≤ (ratioLower (kind i) : ℝ) :=
        Rat.cast_le.mpr (ratio_bounds (kind i)).1
      norm_num at hh
      exact hh
    linarith [hlo i hi]
  have hR1 : ∀ i ∈ s, R i ≤ 1 := by
    intro i hi
    have hu : (ratioUpper (kind i) : ℝ) ≤ 1 := by
      exact_mod_cast (ratio_bounds (kind i)).2.2
    exact (hhi i hi).trans hu
  have hp0 := Finset.prod_nonneg hR0
  have hp1 := Finset.prod_le_one hR0 hR1
  have hr : (1 / 2 : ℝ) ≤ r := by
    dsimp [r]
    exact (one_div_le_one_div_of_le (by positivity) (by linarith))
  have hr1 : r ≤ 1 := by
    dsimp [r]
    exact (div_le_one (by positivity)).mpr (by linarith)
  change (c : ℝ) ≤ 1 - r - (a : ℝ) +
    ∑ i ∈ s, (r * (fullExcess (kind i) : ℝ) + (1 - r) * (deletedExcess (kind i) : ℝ))
  by_cases hs3 : s.card = 3
  · obtain ⟨i, j, k, hij, hik, hjk, hs⟩ := Finset.card_eq_three.mp hs3
    have hpLo : (∏ l ∈ s, (ratioLower (kind l) : ℝ)) ≤ ∏ l ∈ s, R l := by
      apply Finset.prod_le_prod _ hlo
      intro l hl
      have hh : (1 / 2 : ℝ) ≤ (ratioLower (kind l) : ℝ) := by
        have hh : (((1 / 2 : ℚ) : ℝ)) ≤ (ratioLower (kind l) : ℝ) :=
          Rat.cast_le.mpr (ratio_bounds (kind l)).1
        norm_num at hh
        exact hh
      linarith
    have hpHi : (∏ l ∈ s, R l) ≤ ∏ l ∈ s, (ratioUpper (kind l) : ℝ) :=
      Finset.prod_le_prod hR0 hhi
    have hl : (threeLower (kind i) (kind j) (kind k) : ℝ) ≤ r := by
      have hh := one_div_le_one_div_of_le (show (0 : ℝ) < 1 + ∏ l ∈ s, R l by positivity)
        (add_le_add le_rfl hpHi)
      simpa [r, threeLower, hs, hij, hik, hjk, mul_assoc] using hh
    have hu : r ≤ (threeUpper (kind i) (kind j) (kind k) : ℝ) := by
      have hpos : (0 : ℝ) < 1 + ∏ l ∈ s, (ratioLower (kind l) : ℝ) := by
        have hh : 0 ≤ ∏ l ∈ s, (ratioLower (kind l) : ℝ) := by
          apply Finset.prod_nonneg
          intro l hl
          have hh : (1 / 2 : ℝ) ≤ (ratioLower (kind l) : ℝ) := by
            have hh : (((1 / 2 : ℚ) : ℝ)) ≤ (ratioLower (kind l) : ℝ) :=
              Rat.cast_le.mpr (ratio_bounds (kind l)).1
            norm_num at hh
            exact hh
          linarith
        linarith
      have hh := one_div_le_one_div_of_le hpos (add_le_add le_rfl hpLo)
      simpa [r, threeUpper, hs, hij, hik, hjk, mul_assoc] using hh
    have hh := three_lower (kind i) (kind j) (kind k) hl hu
    simpa [hs, hij, hik, hjk, mul_add, add_mul, add_assoc, add_left_comm, add_comm] using hh
  · have hk4 : 4 ≤ s.card := by omega
    have hleaf : ∀ i ∈ s, kind i = 0 → 2 / 3 ≤ r := by
      intro i hi hkind
      have hhalf : R i ≤ 1 / 2 := by simpa [hkind, ratioUpper] using hhi i hi
      have hp : (∏ j ∈ s, R j) ≤ 1 / 2 := by
        calc
          (∏ j ∈ s, R j) ≤ ∏ j ∈ s, (if j = i then (1 / 2 : ℝ) else 1) := by
            apply Finset.prod_le_prod hR0
            intro j hj
            split_ifs with he
            · simpa [he] using hhalf
            · exact hR1 j hj
          _ = 1 / 2 := by simp [hi]
      have hh := one_div_le_one_div_of_le (show (0 : ℝ) < 1 + ∏ j ∈ s, R j by positivity)
        (show 1 + ∏ j ∈ s, R j ≤ 3 / 2 by linarith)
      norm_num at hh
      simpa only [r, one_div] using hh
    have hsum := Finset.sum_le_sum (fun i hi =>
      branch_affine_lower (kind i) hr hr1 (hleaf i hi))
    simp only [sum_const, nsmul_eq_mul] at hsum
    exact (high_degree_lower s.card hk4 hr hr1).trans (add_le_add le_rfl hsum)

#print axioms branching_lower
end ForestUnimodality.UnitActivityBranchDensity
