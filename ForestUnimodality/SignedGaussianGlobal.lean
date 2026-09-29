import ForestUnimodality.SignedGaussianHermite

/-! Extension of the true signed Gaussian Hermite envelope beyond the
boundary at which the minimizer becomes zero. -/
namespace ForestUnimodality.SignedGaussianGlobal
open Set Real SignedGaussianProfile SignedGaussianHermite

theorem coefficient_le_half_second {c beta : ℝ}
    (hc : 0 < c) (hc3 : c < 3) (hb : 0 < beta) (hb1 : beta ≤ 1) :
    coefficient c beta ≤ second c 1 / 2 := by
  have hbranch : c * (1 : ℝ) ^ (5 / 2 : ℝ) < 3 := by simpa using hc3
  have hm := MonotoneCurvatureHermite.coefficient_monotone
    (show (1 : ℝ) ∈ Icc beta 1 from ⟨hb1, le_rfl⟩)
    (second_continuousOn hc hb hbranch) (second_strictMonoOn hc hb hbranch).monotoneOn
    (show beta ∈ Icc beta 1 from ⟨le_rfl, hb1⟩)
    (show (1 : ℝ) ∈ Icc beta 1 from ⟨hb1, le_rfl⟩) hb1
  simpa [coefficient, MonotoneCurvatureHermite.coefficient_one] using hm

theorem coefficient_neg {c beta : ℝ}
    (hc : 0 < c) (hc3 : c < 3) (hb : 0 < beta) (hb1 : beta ≤ 1) : coefficient c beta < 0 := by
  have hn := second_neg hc (by norm_num : (0 : ℝ) < 1) (by simpa using hc3)
  have hl := coefficient_le_half_second hc hc3 hb hb1
  linarith

theorem derivative_bound_interior {c beta K y : ℝ}
    (hc : 0 < c) (hc3 : c < 3) (hb : 0 < beta) (hb1 : beta ≤ 1)
    (hK : K ≤ coefficient c beta) (hy : 1 ≤ y) (hbranch : c * y ^ (5 / 2 : ℝ) < 3) :
    first c 1 + 2 * K * (y - 1) ≤ first c y := by
  have hcoef := coefficient_le_half_second hc hc3 hb hb1
  have hmon := (second_strictMonoOn hc hb hbranch).monotoneOn
  let D : ℝ → ℝ := fun t => first c t - (first c 1 + 2 * K * (t - 1))
  have hd (t : ℝ) (ht : t ∈ Icc 1 y) : HasDerivAt D (second c t - 2 * K) t := by
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
    have htbranch : c * t ^ (5 / 2 : ℝ) < 3 :=
      (mul_le_mul_of_nonneg_left (rpow_le_rpow ht0.le ht.2 (by norm_num)) hc.le).trans_lt hbranch
    convert! (first_hasDerivAt hc ht0 htbranch).sub
      ((hasDerivAt_const t (first c 1)).add (((hasDerivAt_id t).sub_const 1).const_mul (2 * K))) using 1
    simp
  have hdm : MonotoneOn D (Icc 1 y) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Icc 1 y := interior_subset ht
      have hm := hmon (show (1 : ℝ) ∈ Icc beta y from ⟨hb1, hy⟩)
        ⟨hb1.trans ht'.1, ht'.2⟩ ht'.1
      rw [(hd t ht').deriv]
      linarith
  have hv := hdm ⟨le_rfl, hy⟩ ⟨hy, le_rfl⟩ hy
  dsimp [D] at hv
  linarith

theorem quadratic_le_profile_below {c beta K y : ℝ}
    (hc : 0 < c) (hc3 : c < 3) (hb : 0 < beta) (hb1 : beta ≤ 1)
    (hK : K ≤ coefficient c beta) (hby : beta ≤ y)
    (hbranch : c * y ^ (5 / 2 : ℝ) < 3) : quadratic c K y ≤ profile c y := by
  have hmax : c * (max 1 y) ^ (5 / 2 : ℝ) < 3 := by
    rcases le_total y 1 with h | h
    · simpa [max_eq_left h] using hc3
    · simpa [max_eq_right h] using hbranch
  exact quadratic_le_profile_interior hc hb ⟨hb1, le_max_left _ _⟩ hmax
    ⟨le_rfl, hb1.trans (le_max_left _ _)⟩ ⟨hby, le_max_right _ _⟩ hby hK

theorem outer_extension {A B K s y : ℝ} (hs : 0 < s) (hK : K ≤ 0)
    (hv : A + B * (s - 1) + K * (s - 1) ^ 2 ≤ s ^ (-(3 / 2 : ℝ)))
    (hd : B + 2 * K * (s - 1) ≤ -(3 / 2 : ℝ) * s ^ (-(5 / 2 : ℝ))) (hy : s ≤ y) :
    A + B * (y - 1) + K * (y - 1) ^ 2 ≤ y ^ (-(3 / 2 : ℝ)) := by
  let f : ℝ → ℝ := fun t => t ^ (-(3 / 2 : ℝ)) - (A + B * (t - 1) + K * (t - 1) ^ 2)
  let g : ℝ → ℝ := fun t => -(3 / 2 : ℝ) * t ^ (-(5 / 2 : ℝ)) - (B + 2 * K * (t - 1))
  have hdf (t : ℝ) (ht : s ≤ t) : HasDerivAt f (g t) t := by
    have ht0 : 0 < t := hs.trans_le ht
    have hp := (hasDerivAt_id t).rpow_const (p := -(3 / 2 : ℝ)) (Or.inl ht0.ne')
    have hlin := (hasDerivAt_id t).sub_const 1
    convert! hp.sub (((hasDerivAt_const t A).add (hlin.const_mul B)).add ((hlin.pow 2).const_mul K)) using 1
    dsimp [f, g]
    norm_num
    ring
  have hdg (t : ℝ) (ht : s ≤ t) : HasDerivAt g
      ((15 / 4 : ℝ) * t ^ (-(7 / 2 : ℝ)) - 2 * K) t := by
    have ht0 : 0 < t := hs.trans_le ht
    have hp := ((hasDerivAt_id t).rpow_const (p := -(5 / 2 : ℝ)) (Or.inl ht0.ne')).const_mul (-(3 / 2 : ℝ))
    convert! hp.sub ((hasDerivAt_const t B).add (((hasDerivAt_id t).sub_const 1).const_mul (2 * K))) using 1
    dsimp [g]
    norm_num
    ring
  have hgm : MonotoneOn g (Ici s) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · exact fun t ht => (hdg t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hdg t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : s ≤ t := interior_subset ht
      rw [(hdg t ht').deriv]
      have hp := rpow_pos_of_pos (hs.trans_le ht') (-(7 / 2 : ℝ))
      nlinarith
  have hfm : MonotoneOn f (Ici s) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · exact fun t ht => (hdf t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hdf t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : s ≤ t := interior_subset ht
      rw [(hdf t ht').deriv]
      have hh := hgm (mem_Ici.mpr (le_refl s)) (mem_Ici.mpr ht') ht'
      dsimp [g] at hh ⊢
      linarith
  have hh := hfm (mem_Ici.mpr (le_refl s)) (mem_Ici.mpr hy) hy
  dsimp [f] at hh
  linarith

noncomputable def switchPoint (c : ℝ) : ℝ := (3 / c) ^ (2 / 5 : ℝ)

theorem switchPoint_gt_one {c : ℝ} (hc : 0 < c) (hc3 : c < 3) : 1 < switchPoint c := by
  apply one_lt_rpow
  · exact (lt_div_iff₀ hc).mpr (by simpa using hc3)
  · norm_num

theorem switchPoint_equation {c : ℝ} (hc : 0 < c) :
    c * switchPoint c ^ (5 / 2 : ℝ) = 3 := by
  unfold switchPoint
  rw [← rpow_mul (div_pos (by norm_num : (0 : ℝ) < 3) hc).le]
  norm_num
  field_simp

theorem branch_of_lt_switch {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) (hxs : x < switchPoint c) :
    c * x ^ (5 / 2 : ℝ) < 3 := by
  rw [← switchPoint_equation hc]
  exact mul_lt_mul_of_pos_left (rpow_lt_rpow hx hxs (by norm_num)) hc

/-- Complete unbounded-domain Hermite lower bound for the real minimum
profile, including the transition to the exterior convex branch. -/
theorem quadratic_le_profile {c beta K y : ℝ}
    (hc : 0 < c) (hc3 : c < 3) (hb : 0 < beta) (hb1 : beta ≤ 1)
    (hK : K ≤ coefficient c beta) (hby : beta ≤ y) : quadratic c K y ≤ profile c y := by
  have hs1 := switchPoint_gt_one hc hc3
  have hs0 : 0 < switchPoint c := lt_trans (by norm_num) hs1
  have hswitch := switchPoint_equation hc
  have hclose : closure (Ico (1 : ℝ) (switchPoint c)) = Icc 1 (switchPoint c) :=
    closure_Ico hs1.ne
  have hpcont : ContinuousOn (profile c) (closure (Ico (1 : ℝ) (switchPoint c))) := by
    intro t ht
    rw [hclose] at ht
    exact (profile_continuousAt hc (lt_of_lt_of_le (by norm_num) ht.1)).continuousWithinAt
  have hfcont : ContinuousOn (first c) (closure (Ico (1 : ℝ) (switchPoint c))) := by
    intro t ht
    rw [hclose] at ht
    exact (first_continuousAt hc (lt_of_lt_of_le (by norm_num) ht.1)).continuousWithinAt
  have hscl : switchPoint c ∈ closure (Ico (1 : ℝ) (switchPoint c)) := by
    rw [hclose]
    exact ⟨hs1.le, le_rfl⟩
  have hv : quadratic c K (switchPoint c) ≤ profile c (switchPoint c) := by
    apply le_on_closure (s := Ico (1 : ℝ) (switchPoint c)) (fun t ht =>
      quadratic_le_profile_below hc hc3 hb hb1 hK (hb1.trans ht.1)
        (branch_of_lt_switch hc (lt_of_lt_of_le (by norm_num) ht.1).le ht.2))
      (show ContinuousOn (quadratic c K) (closure (Ico (1 : ℝ) (switchPoint c))) by
        unfold quadratic; fun_prop) hpcont hscl
  have hd : first c 1 + 2 * K * (switchPoint c - 1) ≤ first c (switchPoint c) := by
    apply le_on_closure (s := Ico (1 : ℝ) (switchPoint c)) (fun t ht =>
      derivative_bound_interior hc hc3 hb hb1 hK ht.1
        (branch_of_lt_switch hc (lt_of_lt_of_le (by norm_num) ht.1).le ht.2))
      (by fun_prop) hfcont hscl
  rw [profile_outer (le_of_eq hswitch.symm)] at hv
  rw [first_outer (le_of_eq hswitch.symm)] at hd
  by_cases hys : y < switchPoint c
  · exact quadratic_le_profile_below hc hc3 hb hb1 hK hby
      (branch_of_lt_switch hc (hb.trans_le hby).le hys)
  · have hsy := le_of_not_gt hys
    have hyouter : 3 ≤ c * y ^ (5 / 2 : ℝ) := by
      rw [← hswitch]
      exact mul_le_mul_of_nonneg_left (rpow_le_rpow hs0.le hsy (by norm_num)) hc.le
    rw [profile_outer hyouter]
    exact outer_extension hs0 (hK.trans (coefficient_neg hc hc3 hb hb1).le) hv hd hsy

theorem objective_lower {c beta K y x : ℝ}
    (hc : 0 < c) (hc3 : c < 3) (hb : 0 < beta) (hb1 : beta ≤ 1)
    (hK : K ≤ coefficient c beta) (hby : beta ≤ y) (hx : 0 ≤ x) :
    quadratic c K y ≤ SignedGaussianMinimum.objective c y x :=
  (quadratic_le_profile hc hc3 hb hb1 hK hby).trans
    (profile_lower hc (hb.trans_le hby) hx)

theorem positiveGap_antitone {c alpha beta K : ℝ}
    (hc : 0 < c) (hc3 : c < 3) (ha : 0 < alpha) (hab : alpha ≤ beta) (hb1 : beta ≤ 1) :
    AntitoneOn (positiveGap c K) (Icc alpha beta) := by
  exact SignedGaussianHermite.positiveGap_antitone hc ha ⟨hab.trans hb1, le_rfl⟩
    (by simpa using hc3) ⟨hab, hb1⟩ hb1

#print axioms derivative_bound_interior
#print axioms outer_extension
#print axioms objective_lower
#print axioms positiveGap_antitone
end ForestUnimodality.SignedGaussianGlobal
