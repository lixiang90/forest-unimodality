import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! Exact integral remainders for a function with increasing second derivative.
The same coefficient proves both a Hermite lower envelope and decreasing
positive deficit below the interpolation node. -/
namespace ForestUnimodality.MonotoneCurvatureHermite
open Set MeasureTheory

noncomputable def coefficient (f₂ : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, (1 - s) * f₂ (1 + s * (y - 1))
noncomputable def quadratic (f f₁ f₂ : ℝ → ℝ) (beta y : ℝ) : ℝ :=
  f 1 + f₁ 1 * (y - 1) + coefficient f₂ beta * (y - 1) ^ 2

private theorem affine_mem {l u y s : ℝ} (h1 : (1 : ℝ) ∈ Icc l u)
    (hy : y ∈ Icc l u) (hs : s ∈ Icc 0 1) : 1 + s * (y - 1) ∈ Icc l u := by
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr h1.1),
      mul_nonneg hs.1 (sub_nonneg.mpr hy.1)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr h1.2),
      mul_nonneg hs.1 (sub_nonneg.mpr hy.2)]

private theorem integrand_continuous {f₂ : ℝ → ℝ} {l u y : ℝ}
    (h1 : (1 : ℝ) ∈ Icc l u) (hy : y ∈ Icc l u) (hcont : ContinuousOn f₂ (Icc l u)) :
    ContinuousOn (fun s : ℝ => (1 - s) * f₂ (1 + s * (y - 1))) (Icc 0 1) :=
  (by fun_prop : ContinuousOn (fun s : ℝ => 1 - s) (Icc 0 1)).mul
    (hcont.comp (by fun_prop) (fun s hs => affine_mem h1 hy hs))

theorem identity {f f₁ f₂ : ℝ → ℝ} {l u y : ℝ}
    (h1 : (1 : ℝ) ∈ Icc l u) (hy : y ∈ Icc l u)
    (hd : ∀ x ∈ Icc l u, HasDerivAt f (f₁ x) x)
    (hd₁ : ∀ x ∈ Icc l u, HasDerivAt f₁ (f₂ x) x)
    (hcont : ContinuousOn f₂ (Icc l u)) :
    (y - 1) ^ 2 * coefficient f₂ y = f y - f 1 - f₁ 1 * (y - 1) := by
  let F : ℝ → ℝ := fun s =>
    (1 - s) * ((y - 1) * f₁ (1 + s * (y - 1))) + f (1 + s * (y - 1))
  have hdF (s : ℝ) (hs : s ∈ Icc 0 1) : HasDerivAt F
      ((y - 1) ^ 2 * ((1 - s) * f₂ (1 + s * (y - 1)))) s := by
    have hlin : HasDerivAt (fun t : ℝ => 1 + t * (y - 1)) (y - 1) s := by
      convert! ((hasDerivAt_id s).mul_const (y - 1)).const_add 1 using 1
      simp
    have h0 := (hd _ (affine_mem h1 hy hs)).comp s hlin
    have h1' := (hd₁ _ (affine_mem h1 hy hs)).comp s hlin
    have h := (((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).mul
      (h1'.const_mul (y - 1))).add h0
    convert! h using 1
    dsimp [F]
    ring
  have hi : IntervalIntegrable (fun s : ℝ => (y - 1) ^ 2 *
      ((1 - s) * f₂ (1 + s * (y - 1)))) volume 0 1 :=
    (integrand_continuous h1 hy hcont).intervalIntegrable_of_Icc (by norm_num) |>.const_mul _
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hdF s (by simpa using hs)) hi
  rw [intervalIntegral.integral_const_mul] at he
  dsimp only [F] at he
  simp at he
  unfold coefficient
  linarith

theorem coefficient_monotone {f₂ : ℝ → ℝ} {l u : ℝ}
    (h1 : (1 : ℝ) ∈ Icc l u) (hcont : ContinuousOn f₂ (Icc l u))
    (hmono : MonotoneOn f₂ (Icc l u)) : MonotoneOn (coefficient f₂) (Icc l u) := by
  intro x hx y hy hxy
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((integrand_continuous h1 hx hcont).intervalIntegrable_of_Icc (by norm_num))
    ((integrand_continuous h1 hy hcont).intervalIntegrable_of_Icc (by norm_num))
  intro s hs
  apply mul_le_mul_of_nonneg_left
  · apply hmono (affine_mem h1 hx hs) (affine_mem h1 hy hs)
    nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hxy)]
  · exact sub_nonneg.mpr hs.2

theorem coefficient_one (f₂ : ℝ → ℝ) : coefficient f₂ 1 = f₂ 1 / 2 := by
  unfold coefficient
  simp only [sub_self, mul_zero, add_zero]
  rw [intervalIntegral.integral_mul_const]
  have hi : (∫ s : ℝ in (0 : ℝ)..1, 1 - s) = 1 / 2 := by
    rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun s : ℝ => s)
      (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _)]
    norm_num
  rw [hi]
  ring

theorem gap_identity {f f₁ f₂ : ℝ → ℝ} {l u beta y : ℝ}
    (h1 : (1 : ℝ) ∈ Icc l u) (hy : y ∈ Icc l u)
    (hd : ∀ x ∈ Icc l u, HasDerivAt f (f₁ x) x)
    (hd₁ : ∀ x ∈ Icc l u, HasDerivAt f₁ (f₂ x) x)
    (hcont : ContinuousOn f₂ (Icc l u)) :
    f y - quadratic f f₁ f₂ beta y =
      (coefficient f₂ y - coefficient f₂ beta) * (y - 1) ^ 2 := by
  have he := identity h1 hy hd hd₁ hcont
  unfold quadratic
  nlinarith

theorem quadratic_le {f f₁ f₂ : ℝ → ℝ} {l u beta y : ℝ}
    (h1 : (1 : ℝ) ∈ Icc l u) (hb : beta ∈ Icc l u) (hy : y ∈ Icc l u)
    (hby : beta ≤ y)
    (hd : ∀ x ∈ Icc l u, HasDerivAt f (f₁ x) x)
    (hd₁ : ∀ x ∈ Icc l u, HasDerivAt f₁ (f₂ x) x)
    (hcont : ContinuousOn f₂ (Icc l u)) (hmono : MonotoneOn f₂ (Icc l u)) :
    quadratic f f₁ f₂ beta y ≤ f y := by
  have hg := gap_identity (beta := beta) h1 hy hd hd₁ hcont
  have hC := coefficient_monotone h1 hcont hmono hb hy hby
  nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sq_nonneg (y - 1))]

theorem gap_antitone {f f₁ f₂ : ℝ → ℝ} {l u beta : ℝ}
    (h1 : (1 : ℝ) ∈ Icc l u) (hb : beta ∈ Icc l u) (hb1 : beta ≤ 1)
    (hd : ∀ x ∈ Icc l u, HasDerivAt f (f₁ x) x)
    (hd₁ : ∀ x ∈ Icc l u, HasDerivAt f₁ (f₂ x) x)
    (hcont : ContinuousOn f₂ (Icc l u)) (hmono : MonotoneOn f₂ (Icc l u)) :
    AntitoneOn (fun y => quadratic f f₁ f₂ beta y - f y) (Icc l beta) := by
  intro x hx y hy hxy
  have hx' : x ∈ Icc l u := ⟨hx.1, hx.2.trans hb.2⟩
  have hy' : y ∈ Icc l u := ⟨hy.1, hy.2.trans hb.2⟩
  have hgx := gap_identity (beta := beta) h1 hx' hd hd₁ hcont
  have hgy := gap_identity (beta := beta) h1 hy' hd hd₁ hcont
  have hm := coefficient_monotone h1 hcont hmono
  have hcoef : coefficient f₂ beta - coefficient f₂ y ≤ coefficient f₂ beta - coefficient f₂ x :=
    sub_le_sub_left (hm hx' hy' hxy) _
  have hsq : (y - 1) ^ 2 ≤ (x - 1) ^ 2 := by
    have hy1 := hy.2.trans hb1
    nlinarith
  have hp := mul_le_mul hcoef hsq (sq_nonneg (y - 1))
    (sub_nonneg.mpr (hm hx' hb hx.2))
  nlinarith

/-- Increasing the quadratic penalty may move the zero of the deficit.
Taking the positive part preserves tail monotonicity for every fixed
coefficient, so a certified rational penalty need not equal the exact
Hermite coefficient. -/
theorem positive_gap_antitone {f f₁ f₂ : ℝ → ℝ} {l u beta K : ℝ}
    (h1 : (1 : ℝ) ∈ Icc l u) (hb : beta ∈ Icc l u) (hb1 : beta ≤ 1)
    (hd : ∀ x ∈ Icc l u, HasDerivAt f (f₁ x) x)
    (hd₁ : ∀ x ∈ Icc l u, HasDerivAt f₁ (f₂ x) x)
    (hcont : ContinuousOn f₂ (Icc l u)) (hmono : MonotoneOn f₂ (Icc l u)) :
    AntitoneOn (fun y => max 0 (f 1 + f₁ 1 * (y - 1) + K * (y - 1) ^ 2 - f y))
      (Icc l beta) := by
  have he (y : ℝ) (hy : y ∈ Icc l u) :
      max 0 (f 1 + f₁ 1 * (y - 1) + K * (y - 1) ^ 2 - f y) =
        max 0 (K - coefficient f₂ y) * (y - 1) ^ 2 := by
    have hi := identity h1 hy hd hd₁ hcont
    have hg : f 1 + f₁ 1 * (y - 1) + K * (y - 1) ^ 2 - f y =
        (K - coefficient f₂ y) * (y - 1) ^ 2 := by nlinarith
    rw [hg, max_mul_of_nonneg _ _ (sq_nonneg _), zero_mul]
  intro x hx y hy hxy
  have hx' : x ∈ Icc l u := ⟨hx.1, hx.2.trans hb.2⟩
  have hy' : y ∈ Icc l u := ⟨hy.1, hy.2.trans hb.2⟩
  dsimp only
  rw [he x hx', he y hy']
  have hcoef := max_le_max (le_refl (0 : ℝ))
    (sub_le_sub_left (coefficient_monotone h1 hcont hmono hx' hy' hxy) K)
  have hsq : (y - 1) ^ 2 ≤ (x - 1) ^ 2 := by
    have hy1 := hy.2.trans hb1
    nlinarith
  exact mul_le_mul hcoef hsq (sq_nonneg _) (le_max_left _ _)

#print axioms identity
#print axioms quadratic_le
#print axioms gap_antitone
#print axioms positive_gap_antitone
end ForestUnimodality.MonotoneCurvatureHermite
