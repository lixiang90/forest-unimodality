import ForestUnimodality.SignedGaussianProfile
import ForestUnimodality.MonotoneCurvatureHermite

/-! Hermite statements for the actual signed Gaussian minimum profile.
The interpolation and tail-gap claims have genuine real-domain hypotheses;
the extension beyond the interior-minimum branch is a separate obligation. -/
namespace ForestUnimodality.SignedGaussianHermite
open Set Real SignedGaussianProfile

private theorem interior_branch {c l u x : ℝ} (hc : 0 < c) (hl : 0 < l)
    (hu : c * u ^ (5 / 2 : ℝ) < 3) (hx : x ∈ Icc l u) :
    0 < x ∧ c * x ^ (5 / 2 : ℝ) < 3 := by
  have hx0 := hl.trans_le hx.1
  exact ⟨hx0, (mul_le_mul_of_nonneg_left
    (rpow_le_rpow hx0.le hx.2 (by norm_num)) hc.le).trans_lt hu⟩

theorem second_continuousOn {c l u : ℝ} (hc : 0 < c) (hl : 0 < l)
    (hu : c * u ^ (5 / 2 : ℝ) < 3) : ContinuousOn (second c) (Icc l u) := by
  intro x hx
  have h := interior_branch hc hl hu hx
  exact (second_hasDerivAt hc h.1 h.2).continuousAt.continuousWithinAt

theorem second_strictMonoOn {c l u : ℝ} (hc : 0 < c) (hl : 0 < l)
    (hu : c * u ^ (5 / 2 : ℝ) < 3) : StrictMonoOn (second c) (Icc l u) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (second_continuousOn hc hl hu)
  intro x hx
  have h := interior_branch hc hl hu (interior_subset hx)
  rw [(second_hasDerivAt hc h.1 h.2).deriv]
  exact third_pos hc h.1 h.2

noncomputable def coefficient (c beta : ℝ) : ℝ :=
  MonotoneCurvatureHermite.coefficient (second c) beta
noncomputable def quadratic (c K y : ℝ) : ℝ :=
  profile c 1 + first c 1 * (y - 1) + K * (y - 1) ^ 2
noncomputable def positiveGap (c K y : ℝ) : ℝ := max 0 (quadratic c K y - profile c y)

theorem coefficient_identity {c l u y : ℝ} (hc : 0 < c) (hl : 0 < l)
    (h1 : (1 : ℝ) ∈ Icc l u) (hu : c * u ^ (5 / 2 : ℝ) < 3) (hy : y ∈ Icc l u) :
    (y - 1) ^ 2 * coefficient c y = profile c y - profile c 1 - first c 1 * (y - 1) := by
  apply MonotoneCurvatureHermite.identity h1 hy
  · intro x hx
    have h := interior_branch hc hl hu hx
    exact profile_hasDerivAt hc h.1 h.2
  · intro x hx
    have h := interior_branch hc hl hu hx
    exact first_hasDerivAt hc h.1 h.2
  · exact second_continuousOn hc hl hu

theorem quadratic_le_profile_interior {c l u beta y K : ℝ}
    (hc : 0 < c) (hl : 0 < l) (h1 : (1 : ℝ) ∈ Icc l u)
    (hu : c * u ^ (5 / 2 : ℝ) < 3) (hb : beta ∈ Icc l u) (hy : y ∈ Icc l u)
    (hby : beta ≤ y) (hK : K ≤ coefficient c beta) : quadratic c K y ≤ profile c y := by
  have hid := coefficient_identity hc hl h1 hu hy
  have hm := MonotoneCurvatureHermite.coefficient_monotone h1
    (second_continuousOn hc hl hu) (second_strictMonoOn hc hl hu).monotoneOn hb hy hby
  change coefficient c beta ≤ coefficient c y at hm
  have hp := mul_nonneg (sub_nonneg.mpr (hK.trans hm)) (sq_nonneg (y - 1))
  unfold quadratic
  nlinarith

theorem positiveGap_antitone {c l u beta K : ℝ}
    (hc : 0 < c) (hl : 0 < l) (h1 : (1 : ℝ) ∈ Icc l u)
    (hu : c * u ^ (5 / 2 : ℝ) < 3) (hb : beta ∈ Icc l u) (hb1 : beta ≤ 1) :
    AntitoneOn (positiveGap c K) (Icc l beta) := by
  apply MonotoneCurvatureHermite.positive_gap_antitone h1 hb hb1
  · intro x hx
    have h := interior_branch hc hl hu hx
    exact profile_hasDerivAt hc h.1 h.2
  · intro x hx
    have h := interior_branch hc hl hu hx
    exact first_hasDerivAt hc h.1 h.2
  · exact second_continuousOn hc hl hu
  · exact (second_strictMonoOn hc hl hu).monotoneOn

theorem objective_lower_interior {c l u beta y K x : ℝ}
    (hc : 0 < c) (hl : 0 < l) (h1 : (1 : ℝ) ∈ Icc l u)
    (hu : c * u ^ (5 / 2 : ℝ) < 3) (hb : beta ∈ Icc l u) (hy : y ∈ Icc l u)
    (hby : beta ≤ y) (hK : K ≤ coefficient c beta) (hx : 0 ≤ x) :
    quadratic c K y ≤ SignedGaussianMinimum.objective c y x :=
  (quadratic_le_profile_interior hc hl h1 hu hb hy hby hK).trans
    (profile_lower hc (hl.trans_le hy.1) hx)

#print axioms coefficient_identity
#print axioms quadratic_le_profile_interior
#print axioms positiveGap_antitone
#print axioms objective_lower_interior
end ForestUnimodality.SignedGaussianHermite
