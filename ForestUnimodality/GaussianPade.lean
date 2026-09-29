import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! Full-half-line rational bounds for the actual exponential. Their
remainder signs follow from exact derivatives, with no sampled interval. -/
namespace ForestUnimodality.GaussianPade

open Set Real

def P2 (z : ℝ) : ℝ := 12 - 6 * z + z ^ 2
def Q2 (z : ℝ) : ℝ := 12 + 6 * z + z ^ 2
def P3 (z : ℝ) : ℝ := 120 - 60 * z + 12 * z ^ 2 - z ^ 3
def Q3 (z : ℝ) : ℝ := 120 + 60 * z + 12 * z ^ 2 + z ^ 3

theorem Q2_pos {z : ℝ} (hz : 0 ≤ z) : 0 < Q2 z := by unfold Q2; positivity
theorem Q3_pos {z : ℝ} (hz : 0 ≤ z) : 0 < Q3 z := by unfold Q3; positivity

theorem hasDerivAt_exp_mul_P2_div_Q2 {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt (fun t => exp t * P2 t / Q2 t) (exp z * z ^ 4 / Q2 z ^ 2) z := by
  have hp : HasDerivAt P2 (-6 + 2 * z) z := by
    unfold P2
    convert! ((hasDerivAt_const z (12 : ℝ)).sub ((hasDerivAt_id z).const_mul 6)).add
      ((hasDerivAt_id z).pow 2) using 1
    simp only [id_eq]
    ring
  have hq : HasDerivAt Q2 (6 + 2 * z) z := by
    unfold Q2
    convert! ((hasDerivAt_const z (12 : ℝ)).add ((hasDerivAt_id z).const_mul 6)).add
      ((hasDerivAt_id z).pow 2) using 1
    simp only [id_eq]
    ring
  convert! ((Real.hasDerivAt_exp z).mul hp).div hq (Q2_pos hz).ne' using 1
  simp only [Pi.mul_apply]
  unfold P2 Q2
  ring

theorem hasDerivAt_exp_mul_P3_div_Q3 {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt (fun t => exp t * P3 t / Q3 t) (-exp z * z ^ 6 / Q3 z ^ 2) z := by
  have hp : HasDerivAt P3 (-60 + 24 * z - 3 * z ^ 2) z := by
    unfold P3
    convert! (((hasDerivAt_const z (120 : ℝ)).sub ((hasDerivAt_id z).const_mul 60)).add
      (((hasDerivAt_id z).pow 2).const_mul 12)).sub ((hasDerivAt_id z).pow 3) using 1
    simp only [id_eq]
    ring
  have hq : HasDerivAt Q3 (60 + 24 * z + 3 * z ^ 2) z := by
    unfold Q3
    convert! (((hasDerivAt_const z (120 : ℝ)).add ((hasDerivAt_id z).const_mul 60)).add
      (((hasDerivAt_id z).pow 2).const_mul 12)).add ((hasDerivAt_id z).pow 3) using 1
    simp only [id_eq]
    ring
  convert! ((Real.hasDerivAt_exp z).mul hp).div hq (Q3_pos hz).ne' using 1
  simp only [Pi.mul_apply]
  unfold P3 Q3
  ring

theorem exp_neg_le_P2_div_Q2 {z : ℝ} (hz : 0 ≤ z) : exp (-z) ≤ P2 z / Q2 z := by
  have hm : MonotoneOn (fun t => exp t * P2 t / Q2 t) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · exact fun t ht => (hasDerivAt_exp_mul_P2_div_Q2 ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hasDerivAt_exp_mul_P2_div_Q2 (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht0 : 0 ≤ t := (interior_subset ht : t ∈ Ici 0)
      rw [(hasDerivAt_exp_mul_P2_div_Q2 ht0).deriv]
      positivity
  have hb : 1 ≤ exp z * P2 z / Q2 z := by
    simpa [P2, Q2] using hm (by simp : (0 : ℝ) ∈ Ici 0) hz hz
  have he : exp (-z) * exp z = 1 := by rw [← Real.exp_add]; simp
  calc
    exp (-z) = exp (-z) * 1 := by ring
    _ ≤ exp (-z) * (exp z * P2 z / Q2 z) :=
      mul_le_mul_of_nonneg_left hb (exp_pos _).le
    _ = (exp (-z) * exp z) * (P2 z / Q2 z) := by ring
    _ = P2 z / Q2 z := by rw [he, one_mul]

theorem P3_div_Q3_le_exp_neg {z : ℝ} (hz : 0 ≤ z) : P3 z / Q3 z ≤ exp (-z) := by
  have hm : AntitoneOn (fun t => exp t * P3 t / Q3 t) (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · exact fun t ht => (hasDerivAt_exp_mul_P3_div_Q3 ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hasDerivAt_exp_mul_P3_div_Q3 (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht0 : 0 ≤ t := (interior_subset ht : t ∈ Ici 0)
      rw [(hasDerivAt_exp_mul_P3_div_Q3 ht0).deriv]
      exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (exp_pos _).le) (by positivity)) (sq_nonneg _)
  have hb : exp z * P3 z / Q3 z ≤ 1 := by
    simpa [P3, Q3] using hm (by simp : (0 : ℝ) ∈ Ici 0) hz hz
  have he : exp (-z) * exp z = 1 := by rw [← Real.exp_add]; simp
  calc
    P3 z / Q3 z = (exp (-z) * exp z) * (P3 z / Q3 z) := by rw [he, one_mul]
    _ = exp (-z) * (exp z * P3 z / Q3 z) := by ring
    _ ≤ exp (-z) * 1 := mul_le_mul_of_nonneg_left hb (exp_pos _).le
    _ = exp (-z) := by ring

#print axioms exp_neg_le_P2_div_Q2
#print axioms P3_div_Q3_le_exp_neg

end ForestUnimodality.GaussianPade
