import ForestUnimodality.ExactLogCapacity
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace ForestUnimodality

/-- Continuous source cells may safely use the exact logarithmic weight at
their lower probability endpoint, including a cell starting at zero. -/
theorem sourceExactH_antitone : AntitoneOn sourceExactH (Set.Ico (0 : ℝ) 1) := by
  let f : ℝ → ℝ := fun p => p / (-Real.log (1 - p))
  have hd : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt f
      ((-Real.log (1 - x) - x * (1 / (1 - x))) / (-Real.log (1 - x)) ^ 2) x := by
    intro x hx
    have hlog : 0 < -Real.log (1 - x) :=
      neg_pos.mpr (Real.log_neg (by linarith [hx.2]) (by linarith [hx.1]))
    have hi : HasDerivAt (fun p : ℝ => 1 - p) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 1
    have hl : HasDerivAt (fun p : ℝ => -Real.log (1 - p)) (1 / (1 - x)) x := by
      have hne : 1 - x ≠ 0 := (sub_pos.mpr hx.2).ne'
      convert (hi.log hne).neg using 1
      all_goals first | rfl | (norm_num; ring)
    convert (hasDerivAt_id x).div hl hlog.ne' using 1
    all_goals first | rfl | norm_num
  have hanti : AntitoneOn f (Set.Ioo (0 : ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 1)
    · intro x hx
      exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hxi : x ∈ Set.Ioo (0 : ℝ) 1 := interior_subset hx
      rw [(hd x hxi).deriv]
      have hb := Real.log_le_sub_one_of_pos (inv_pos.mpr (sub_pos.mpr hxi.2))
      rw [Real.log_inv] at hb
      have he : (1 - x)⁻¹ - 1 = x * (1 / (1 - x)) := by
        field_simp [(sub_pos.mpr hxi.2).ne']
        ring
      rw [he] at hb
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hb) (sq_nonneg _)
  intro x hx y hy hxy
  by_cases hx0 : x = 0
  · subst x
    rw [show sourceExactH 0 = 1 by simp [sourceExactH]]
    have hh := sourceExactH_le_relaxed hy.1 hy.2
    have hy0 : 0 ≤ y := hy.1
    change sourceExactH y ≤ 1
    linarith
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    have hypos : 0 < y := hxpos.trans_le hxy
    have hh := hanti ⟨hxpos, hx.2⟩ ⟨hypos, hy.2⟩ hxy
    simpa only [sourceExactH, if_neg hx0, if_neg hypos.ne', f] using hh

#print axioms sourceExactH_antitone
end ForestUnimodality
