import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! Exact triangular lattice kernel and its finite-period Gaussian error.
The estimates concern actual real trigonometric and exponential functions;
there is no sampled-point or asymptotic remainder premise. -/
namespace ForestUnimodality.TriangularGaussian
open Set Real

noncomputable def kernel (t : ℝ) : ℝ := Real.sinc (t / 2) ^ 2

theorem lattice_identity (t : ℝ) : t ^ 2 * kernel t = 2 - 2 * Real.cos t := by
  by_cases ht : t = 0
  · simp [ht, kernel]
  rw [kernel, Real.sinc_of_ne_zero (by exact div_ne_zero ht (by norm_num))]
  have hc := Real.cos_two_mul (t / 2)
  have hs := Real.sin_sq_add_cos_sq (t / 2)
  have he : 2 * (t / 2) = t := by ring
  rw [he] at hc
  field_simp
  nlinarith

private theorem nonneg_of_deriv {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hzero : 0 ≤ f 0)
    (hd : ∀ x, 0 < x → 0 ≤ deriv f x) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hm := monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
    hf.continuous.continuousOn hf.differentiableOn
    (fun x hx => hd x (by simpa using hx))
  exact hzero.trans (hm (by simp) hx hx)

theorem cos_le_taylor_eight {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 := by
  have h4 (t : ℝ) (ht : 0 ≤ t) : 0 ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t := by
    apply nonneg_of_deriv (f := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t)
      (by fun_prop) (by norm_num) ?_ ht
    intro y hy
    have hs := Real.sin_ge_sub_cube hy.le
    simp (disch := fun_prop)
    nlinarith
  have h5 (t : ℝ) (ht : 0 ≤ t) : 0 ≤ t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t := by
    apply nonneg_of_deriv (f := fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t)
      (by fun_prop) (by norm_num) ?_ ht
    intro y hy
    have hs := h4 y hy.le
    simp (disch := fun_prop)
    nlinarith
  have h6 (t : ℝ) (ht : 0 ≤ t) :
      0 ≤ Real.cos t - 1 + t ^ 2 / 2 - t ^ 4 / 24 + t ^ 6 / 720 := by
    apply nonneg_of_deriv (f := fun t => Real.cos t - 1 + t ^ 2 / 2 - t ^ 4 / 24 + t ^ 6 / 720)
      (by fun_prop) (by norm_num) ?_ ht
    intro y hy
    have hs := h5 y hy.le
    simp (disch := fun_prop)
    nlinarith
  have h7 (t : ℝ) (ht : 0 ≤ t) :
      0 ≤ Real.sin t - t + t ^ 3 / 6 - t ^ 5 / 120 + t ^ 7 / 5040 := by
    apply nonneg_of_deriv (f := fun t => Real.sin t - t + t ^ 3 / 6 - t ^ 5 / 120 + t ^ 7 / 5040)
      (by fun_prop) (by norm_num) ?_ ht
    intro y hy
    have hs := h6 y hy.le
    simp (disch := fun_prop)
    nlinarith
  have h8 : 0 ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - Real.cos x := by
    apply nonneg_of_deriv (f := fun t =>
      1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - Real.cos t)
      (by fun_prop) (by norm_num) ?_ hx
    intro y hy
    have hs := h7 y hy.le
    simp (disch := fun_prop)
    nlinarith
  linarith

theorem exp_neg_le_taylor_four {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 := by
  have h1 (t : ℝ) (ht : 0 ≤ t) : 0 ≤ Real.exp (-t) - 1 + t := by
    apply nonneg_of_deriv (f := fun t => Real.exp (-t) - 1 + t)
      (by fun_prop) (by norm_num) ?_ ht
    intro y hy
    have he : Real.exp (-y) ≤ 1 := by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
    simp (disch := fun_prop)
    linarith
  have h2 (t : ℝ) (ht : 0 ≤ t) : 0 ≤ 1 - t + t ^ 2 / 2 - Real.exp (-t) := by
    apply nonneg_of_deriv (f := fun t => 1 - t + t ^ 2 / 2 - Real.exp (-t))
      (by fun_prop) (by norm_num) ?_ ht
    intro y hy
    have he := h1 y hy.le
    simp (disch := fun_prop)
    linarith
  have h3 (t : ℝ) (ht : 0 ≤ t) :
      0 ≤ Real.exp (-t) - 1 + t - t ^ 2 / 2 + t ^ 3 / 6 := by
    apply nonneg_of_deriv (f := fun t => Real.exp (-t) - 1 + t - t ^ 2 / 2 + t ^ 3 / 6)
      (by fun_prop) (by norm_num) ?_ ht
    intro y hy
    have he := h2 y hy.le
    simp (disch := fun_prop)
    nlinarith
  have h4 : 0 ≤ 1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 - Real.exp (-x) := by
    apply nonneg_of_deriv (f := fun t => 1 - t + t ^ 2 / 2 - t ^ 3 / 6 + t ^ 4 / 24 - Real.exp (-t))
      (by fun_prop) (by norm_num) ?_ hx
    intro y hy
    have he := h3 y hy.le
    simp (disch := fun_prop)
    nlinarith
  linarith

private theorem sin_sub_mul_cos_nonneg {x : ℝ} (hx : 0 ≤ x) (hpi : x ≤ Real.pi) :
    0 ≤ Real.sin x - x * Real.cos x := by
  have hm : MonotoneOn (fun t => Real.sin t - t * Real.cos t) (Icc 0 Real.pi) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (by fun_prop) (by fun_prop)
    intro t ht
    have ht' : t ∈ Ioo 0 Real.pi := by simpa only [interior_Icc] using ht
    have hs := mul_nonneg ht'.1.le (Real.sin_nonneg_of_nonneg_of_le_pi ht'.1.le ht'.2.le)
    simp (disch := fun_prop)
    nlinarith
  have he := hm ⟨le_rfl, Real.pi_pos.le⟩ ⟨hx, hpi⟩ hx
  simpa using he

private theorem gaussian_sine_comparison {x : ℝ} (hx : 0 ≤ x) (hpi : x ≤ Real.pi) :
    0 ≤ (1 - x ^ 2 / 3) * Real.sin x - x * Real.cos x := by
  have hm : MonotoneOn
      (fun t => (1 - t ^ 2 / 3) * Real.sin t - t * Real.cos t) (Icc 0 Real.pi) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (by fun_prop) (by fun_prop)
    intro t ht
    have ht' : t ∈ Ioo 0 Real.pi := by simpa only [interior_Icc] using ht
    have hs := mul_nonneg ht'.1.le (sin_sub_mul_cos_nonneg ht'.1.le ht'.2.le)
    simp (disch := fun_prop)
    nlinarith
  have he := hm ⟨le_rfl, Real.pi_pos.le⟩ ⟨hx, hpi⟩ hx
  simpa using he

theorem sinc_le_gaussian {x : ℝ} (hx : 0 ≤ x) (hpi : x ≤ Real.pi / 2) :
    Real.sinc x ≤ Real.exp (-(x ^ 2) / 6) := by
  let f : ℝ → ℝ := fun t => Real.exp (t ^ 2 / 6) * Real.sinc t
  have hd (t : ℝ) (ht : t ≠ 0) : HasDerivAt f
      (Real.exp (t ^ 2 / 6) * (t * Real.cos t - (1 - t ^ 2 / 3) * Real.sin t) / t ^ 2) t := by
    have he : f =ᶠ[nhds t] (fun y => Real.exp (y ^ 2 / 6) * (Real.sin y / y)) := by
      filter_upwards [eventually_ne_nhds ht] with y hy
      simp only [f, Real.sinc_of_ne_zero hy]
    have hd := (((hasDerivAt_id t).pow 2).div_const 6).exp.mul
      ((Real.hasDerivAt_sin t).div (hasDerivAt_id t) ht)
    convert! hd.congr_of_eventuallyEq he using 1
    simp only [Pi.pow_apply, Pi.div_apply, id_eq, Nat.reduceSub, Nat.cast_ofNat]
    field_simp [ht]
    ring
  have hm : AntitoneOn f (Icc 0 (Real.pi / 2)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) (by dsimp [f]; fun_prop)
    · intro t ht
      have ht' : t ∈ Ioo 0 (Real.pi / 2) := by simpa only [interior_Icc] using ht
      exact (hd t ht'.1.ne').differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Ioo 0 (Real.pi / 2) := by simpa only [interior_Icc] using ht
      rw [(hd t ht'.1.ne').deriv]
      apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg t)
      apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      have hg := gaussian_sine_comparison ht'.1.le (by have ht2 := ht'.2; linarith [Real.pi_pos])
      linarith
  have hh : Real.exp (x ^ 2 / 6) * Real.sinc x ≤ 1 := by
    have he := hm ⟨le_rfl, by positivity⟩ ⟨hx, hpi⟩ hx
    simpa [f] using he
  have he : Real.exp (-(x ^ 2) / 6) * Real.exp (x ^ 2 / 6) = 1 := by
    rw [← Real.exp_add]
    have hz : -(x ^ 2) / 6 + x ^ 2 / 6 = 0 := by ring
    rw [hz, Real.exp_zero]
  have hmul := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-(x ^ 2) / 6)).le
  rwa [← mul_assoc, he, one_mul, mul_one] at hmul

theorem kernel_lower_taylor {t : ℝ} (ht : 0 ≤ t) :
    1 - t ^ 2 / 12 + t ^ 4 / 360 - t ^ 6 / 20160 ≤ kernel t := by
  by_cases he : t = 0
  · simp [he, kernel]
  have hc := cos_le_taylor_eight ht
  have hid := lattice_identity t
  apply (mul_le_mul_iff_of_pos_left (sq_pos_of_ne_zero he)).mp
  nlinarith

theorem gaussian_error_upper_of_nonneg {t : ℝ} (ht : 0 ≤ t) (hpi : t ≤ Real.pi) :
    Real.exp (-(t ^ 2) / 12) - kernel t ≤ t ^ 4 / 1440 := by
  have htbound : t ≤ (63 / 20 : ℝ) := by linarith [Real.pi_lt_d2]
  have hsquare : t ^ 2 ≤ 10 := by nlinarith
  have hcos := kernel_lower_taylor ht
  have he := exp_neg_le_taylor_four (x := t ^ 2 / 12) (by positivity)
  have hpow : t ^ 8 ≤ 10 * t ^ 6 := by
    have hm := mul_nonneg (pow_nonneg ht 6) (sub_nonneg.mpr hsquare)
    nlinarith
  have h6 := pow_nonneg ht 6
  have hexp : -(t ^ 2 / 12) = -(t ^ 2) / 12 := by ring
  rw [hexp] at he
  nlinarith

theorem gaussian_error_nonneg_of_nonneg {t : ℝ} (ht : 0 ≤ t) (hpi : t ≤ Real.pi) :
    0 ≤ Real.exp (-(t ^ 2) / 12) - kernel t := by
  have hs := sinc_le_gaussian (x := t / 2) (by positivity) (by linarith)
  have hnonneg : 0 ≤ Real.sinc (t / 2) := by
    by_cases he : t / 2 = 0
    · simp [he]
    rw [Real.sinc_of_ne_zero he]
    exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
      (by linarith [Real.pi_pos])) (by positivity)
  have hsq : Real.sinc (t / 2) ^ 2 ≤ Real.exp (-((t / 2) ^ 2) / 6) ^ 2 := by
    exact pow_le_pow_left₀ hnonneg hs 2
  have he : Real.exp (-((t / 2) ^ 2) / 6) ^ 2 = Real.exp (-(t ^ 2) / 12) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he] at hsq
  exact sub_nonneg.mpr hsq

theorem gaussian_error_bounds {t : ℝ} (ht : |t| ≤ Real.pi) :
    0 ≤ Real.exp (-(t ^ 2) / 12) - kernel t ∧
      Real.exp (-(t ^ 2) / 12) - kernel t ≤ t ^ 4 / 1440 := by
  rcases le_or_gt 0 t with hn | hn
  · exact ⟨gaussian_error_nonneg_of_nonneg hn (abs_le.mp ht).2,
      gaussian_error_upper_of_nonneg hn (abs_le.mp ht).2⟩
  · have hpi : -t ≤ Real.pi := by linarith [(abs_le.mp ht).1]
    have h0 := gaussian_error_nonneg_of_nonneg (neg_nonneg.mpr hn.le) hpi
    have h1 := gaussian_error_upper_of_nonneg (neg_nonneg.mpr hn.le) hpi
    have he : (-t) ^ 4 = t ^ 4 := by ring
    simpa only [kernel, neg_div, Real.sinc_neg, neg_sq, he] using And.intro h0 h1

theorem kernel_nonneg (t : ℝ) : 0 ≤ kernel t := sq_nonneg _

theorem kernel_le_one (t : ℝ) : kernel t ≤ 1 := by
  have h := Real.abs_sinc_le_one (t / 2)
  have hs : Real.sinc (t / 2) ^ 2 ≤ 1 := by nlinarith [abs_le.mp h |>.1, abs_le.mp h |>.2]
  exact hs

/-- The exact variance-matched curvature-frequency error. No restriction
on the Gaussian parameter is needed for this pointwise estimate. -/
theorem variance_matched_error_bounds (a : ℝ) {t : ℝ} (ht : |t| ≤ Real.pi) :
    0 ≤ t ^ 2 * Real.exp (-(a + 1 / 6) * t ^ 2 / 2) -
      t ^ 2 * kernel t * Real.exp (-a * t ^ 2 / 2) ∧
    t ^ 2 * Real.exp (-(a + 1 / 6) * t ^ 2 / 2) -
      t ^ 2 * kernel t * Real.exp (-a * t ^ 2 / 2) ≤
        t ^ 6 / 1440 * Real.exp (-a * t ^ 2 / 2) := by
  have he : Real.exp (-(a + 1 / 6) * t ^ 2 / 2) =
      Real.exp (-a * t ^ 2 / 2) * Real.exp (-(t ^ 2) / 12) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hid : t ^ 2 * Real.exp (-(a + 1 / 6) * t ^ 2 / 2) -
      t ^ 2 * kernel t * Real.exp (-a * t ^ 2 / 2) =
      (t ^ 2 * Real.exp (-a * t ^ 2 / 2)) * (Real.exp (-(t ^ 2) / 12) - kernel t) := by
    rw [he]
    ring
  rw [hid]
  have hfactor := mul_nonneg (sq_nonneg t) (Real.exp_pos (-a * t ^ 2 / 2)).le
  have hb := gaussian_error_bounds ht
  refine ⟨mul_nonneg hfactor hb.1, ?_⟩
  calc
    _ ≤ (t ^ 2 * Real.exp (-a * t ^ 2 / 2)) * (t ^ 4 / 1440) :=
      mul_le_mul_of_nonneg_left hb.2 hfactor
    _ = _ := by ring

#print axioms lattice_identity
#print axioms cos_le_taylor_eight
#print axioms exp_neg_le_taylor_four
#print axioms sinc_le_gaussian
#print axioms gaussian_error_bounds
#print axioms variance_matched_error_bounds
end ForestUnimodality.TriangularGaussian


