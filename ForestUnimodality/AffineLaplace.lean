import ForestUnimodality.HeterogeneousHardCore
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Integrating an affine variance bound along one fixed exponential tilt.
This is a finite-distribution statement, with no reoptimization of marks. -/
namespace ForestUnimodality.AffineLaplace
open Set

noncomputable def decayIntegral (C u : ℝ) : ℝ := (1 - Real.exp (-C*u))/C

theorem hasDerivAt_decayIntegral {C : ℝ} (hC : C ≠ 0) (u : ℝ) :
    HasDerivAt (decayIntegral C) (Real.exp (-C*u)) u := by
  apply (((((hasDerivAt_id u).const_mul (-C)).exp).const_sub 1).div_const C).congr_deriv
  dsimp
  field_simp

/-- The integrating factor proof keeps the continuous boundary u=0. -/
theorem mean_lower {w v : ℝ → ℝ} {D C u : ℝ} (hC : 0 < C) (hu : 0 ≤ u)
    (hd : ∀ t ∈ Icc 0 u, HasDerivAt w (-v t) t)
    (hv : ∀ t ∈ Icc 0 u, v t ≤ D + C*w t) :
    (w 0 + D/C)*Real.exp (-C*u)-D/C ≤ w u := by
  let f := fun t : ℝ => Real.exp (C*t)*(w t+D/C)
  have hf (t : ℝ) (ht : t ∈ Icc 0 u) :
      HasDerivAt f (Real.exp (C*t)*(D+C*w t-v t)) t := by
    apply ((((hasDerivAt_id t).const_mul C).exp).mul ((hd t ht).add_const (D/C))).congr_deriv
    dsimp
    field_simp
    ring
  have hm : MonotoneOn f (Icc 0 u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro t ht; exact (hf t ht).continuousAt.continuousWithinAt
    · intro t ht; exact (hf t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hf t (interior_subset ht)).deriv]
      exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (hv t (interior_subset ht)))
  have h := hm ⟨le_rfl,hu⟩ ⟨hu,le_rfl⟩ hu
  dsimp [f] at h
  simp only [mul_zero, Real.exp_zero, one_mul] at h
  have hh := mul_le_mul_of_nonneg_left h (Real.exp_pos (-C*u)).le
  have he : Real.exp (-C*u)*Real.exp (C*u)=1 := by rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  rw [← mul_assoc, he, one_mul] at hh
  nlinarith

theorem log_lower_tilt_bound {w v L : ℝ → ℝ} {D C u : ℝ}
    (hC : 0 < C) (hu : 0 ≤ u)
    (hw : ∀ t ∈ Icc 0 u, HasDerivAt w (-v t) t)
    (hL : ∀ t ∈ Icc 0 u, HasDerivAt L (-w t) t)
    (hv : ∀ t ∈ Icc 0 u, v t ≤ D+C*w t) :
    L u-L 0 ≤ -w 0*decayIntegral C u + D/C*(u-decayIntegral C u) := by
  let f := fun t : ℝ => L t + w 0*decayIntegral C t - D/C*(t-decayIntegral C t)
  have hf (t : ℝ) (ht : t ∈ Icc 0 u) : HasDerivAt f
      (-w t + w 0*Real.exp (-C*t)-D/C*(1-Real.exp (-C*t))) t := by
    exact ((hL t ht).add ((hasDerivAt_decayIntegral (ne_of_gt hC) t).const_mul (w 0))).sub
      (((hasDerivAt_id t).sub (hasDerivAt_decayIntegral (ne_of_gt hC) t)).const_mul (D/C))
  have hm : AntitoneOn f (Icc 0 u) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · intro t ht; exact (hf t ht).continuousAt.continuousWithinAt
    · intro t ht; exact (hf t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have hts := interior_subset ht
      have hbound := mean_lower hC hts.1
        (fun s hs => hw s ⟨hs.1,hs.2.trans hts.2⟩)
        (fun s hs => hv s ⟨hs.1,hs.2.trans hts.2⟩)
      rw [(hf t hts).deriv]
      nlinarith
  have h := hm ⟨le_rfl,hu⟩ ⟨hu,le_rfl⟩ hu
  dsimp [f] at h
  simp only [decayIntegral, mul_zero, Real.exp_zero, sub_self, zero_div, mul_zero,
    add_zero, sub_zero] at h ⊢
  linarith

#print axioms mean_lower
#print axioms log_lower_tilt_bound
end ForestUnimodality.AffineLaplace

namespace ForestUnimodality.FiniteTilt
open Finset Set

theorem mean_neg {α : Type*} (s : Finset α) (w X : α → ℝ) :
    mean s w (fun x => -X x) = -mean s w X := by
  simp only [mean, numerator, mul_neg, sum_neg_distrib, neg_div]

theorem covariance_neg_right {α : Type*} (s : Finset α) (w X Y : α → ℝ) :
    covariance s w X (fun x => -Y x) = -covariance s w X Y := by
  simp only [covariance, mul_neg, mean_neg]
  ring

theorem total_tilt_pos {α : Type*} (s : Finset α) (w X : α → ℝ)
    (hw : ∀ x ∈ s, 0 ≤ w x) (hZ : 0 < total s w) (t : ℝ) :
    0 < total s (tilt w X t) := by
  obtain ⟨x,hx,hpos⟩ := (sum_pos_iff_of_nonneg hw).mp hZ
  apply (sum_pos_iff_of_nonneg (fun y hy => mul_nonneg (hw y hy) (Real.exp_pos _).le)).mpr
  exact ⟨x,hx,mul_pos hpos (Real.exp_pos _)⟩

theorem log_laplace_le_of_affine_variance {α : Type*} (s : Finset α) (w X : α → ℝ)
    (hw : ∀ x ∈ s, 0 ≤ w x) (hZ : 0 < total s w) {D C u : ℝ}
    (hC : 0 < C) (hu : 0 ≤ u)
    (hv : ∀ t ∈ Icc 0 u,
      variance s (tilt w (fun x => -X x) t) X ≤
        D+C*mean s (tilt w (fun x => -X x) t) X) :
    Real.log (total s (tilt w (fun x => -X x) u) / total s w) ≤
      -mean s w X * AffineLaplace.decayIntegral C u +
        D/C*(u-AffineLaplace.decayIntegral C u) := by
  have hz (t : ℝ) := total_tilt_pos s w (fun x => -X x) hw hZ t
  have hmean (t : ℝ) : HasDerivAt (fun t => mean s (tilt w (fun x => -X x) t) X)
      (-variance s (tilt w (fun x => -X x) t) X) t := by
    simpa only [covariance_neg_right, variance] using
      hasDerivAt_mean s w (fun x => -X x) X t (ne_of_gt (hz t))
  have hlog (t : ℝ) : HasDerivAt (fun t => Real.log (total s (tilt w (fun x => -X x) t)))
      (-mean s (tilt w (fun x => -X x) t) X) t := by
    have h := (hasDerivAt_total s w (fun x => -X x) t).log (ne_of_gt (hz t))
    change HasDerivAt _ (mean s (tilt w (fun x => -X x) t) (fun x => -X x)) t at h
    simpa only [mean_neg] using h
  have h := AffineLaplace.log_lower_tilt_bound hC hu (fun t _ => hmean t)
    (fun t _ => hlog t) hv
  have ht : tilt w (fun x => -X x) 0 = w := by funext x; simp [tilt]
  rw [ht] at h
  rwa [Real.log_div (ne_of_gt (hz u)) (ne_of_gt hZ)]

#print axioms log_laplace_le_of_affine_variance
end ForestUnimodality.FiniteTilt
