import ForestUnimodality.FiniteStirling
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Finite Bernoulli relative entropy along an actual parameter segment. -/
namespace ForestUnimodality.BernoulliEntropy
open Real Set MeasureTheory

noncomputable def divergence (q p : ℝ) : ℝ :=
  p * (Real.log p - Real.log q) + (1 - p) * (Real.log (1 - p) - Real.log (1 - q))

noncomputable def logOddsChange (q p : ℝ) : ℝ :=
  Real.log p - Real.log q - Real.log (1 - p) + Real.log (1 - q)

theorem path_mem {q h t : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hp : q + h ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    q + t * h ∈ Ioo (0 : ℝ) 1 := by
  have he := (convex_Ioo (0 : ℝ) 1) hq hp (sub_nonneg.mpr ht.2) ht.1
    (show 1 - t + t = 1 by ring)
  convert he using 1
  simp only [smul_eq_mul]
  ring

theorem hasDerivAt_logOddsChange {q h t : ℝ} (hp : q + t * h ≠ 0)
    (hp' : 1 - (q + t * h) ≠ 0) :
    HasDerivAt (fun x => logOddsChange q (q + x * h))
      (h / ((q + t * h) * (1 - (q + t * h)))) t := by
  have hx : HasDerivAt (fun x : ℝ => q + x * h) h t := by
    convert! (hasDerivAt_const t q).add ((hasDerivAt_id t).mul_const h) using 1
    simp
  have hy := (hasDerivAt_const t 1).sub hx
  unfold logOddsChange
  convert! (((hx.log hp).sub_const (Real.log q)).sub (hy.log hp')).add_const
    (Real.log (1 - q)) using 1
  simp only [zero_sub, Pi.sub_apply]
  generalize q + t * h = x at hp hp' ⊢
  field_simp [hp, hp']
  ring

theorem hasDerivAt_divergence {q h t : ℝ} (hp : q + t * h ≠ 0)
    (hp' : 1 - (q + t * h) ≠ 0) :
    HasDerivAt (fun x => divergence q (q + x * h))
      (h * logOddsChange q (q + t * h)) t := by
  have hx : HasDerivAt (fun x : ℝ => q + x * h) h t := by
    convert! (hasDerivAt_const t q).add ((hasDerivAt_id t).mul_const h) using 1
    simp
  have hy := (hasDerivAt_const t 1).sub hx
  unfold divergence
  convert! (hx.mul ((hx.log hp).sub_const (Real.log q))).add
    (hy.mul ((hy.log hp').sub_const (Real.log (1 - q)))) using 1
  dsimp [logOddsChange]
  simp only [zero_sub]
  generalize q + t * h = x at hp hp' ⊢
  field_simp [hp, hp']
  ring

theorem divergence_integral {q h : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hp : q + h ∈ Ioo (0 : ℝ) 1) :
    divergence q (q + h) = ∫ t in (0 : ℝ)..1,
      h ^ 2 * (1 - t) / ((q + t * h) * (1 - (q + t * h))) := by
  let F : ℝ → ℝ := fun t => divergence q (q + t * h) +
    (1 - t) * h * logOddsChange q (q + t * h)
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt F (h ^ 2 * (1 - t) / ((q + t * h) * (1 - (q + t * h)))) t := by
    have hm := path_mem hq hp ht
    have hxp : q + t * h ≠ 0 := hm.1.ne'
    have hyp : 1 - (q + t * h) ≠ 0 := ne_of_gt (sub_pos.mpr hm.2)
    convert! (hasDerivAt_divergence hxp hyp).add
      ((((hasDerivAt_const t 1).sub (hasDerivAt_id t)).mul_const h).mul
        (hasDerivAt_logOddsChange hxp hyp)) using 1
    simp only [zero_sub, Pi.sub_apply, id_eq]
    field_simp
    ring
  have hc : ContinuousOn (fun t : ℝ =>
      h ^ 2 * (1 - t) / ((q + t * h) * (1 - (q + t * h)))) (Icc 0 1) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    have hm := path_mem hq hp ht
    exact mul_ne_zero hm.1.ne' (ne_of_gt (sub_pos.mpr hm.2))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa using ht)) (hc.intervalIntegrable_of_Icc (by norm_num))
  dsimp [F] at he
  simpa [divergence, logOddsChange] using he.symm

theorem weighted_variance_integral (q h : ℝ) :
    (∫ t in (0 : ℝ)..1, (1 - t) * ((q + t * h) * (1 - (q + t * h)))) =
      (q * (1 - q) + (1 - 2 * q) * h / 3 - h ^ 2 / 6) / 2 := by
  let A := q * (1 - q)
  let B := (1 - 2 * q) * h - A
  let C := h ^ 2 + (1 - 2 * q) * h
  let F : ℝ → ℝ := fun t => A * t + B * t ^ 2 / 2 - C * t ^ 3 / 3 + h ^ 2 * t ^ 4 / 4
  have hd (t : ℝ) : HasDerivAt F ((1 - t) * ((q + t * h) * (1 - (q + t * h)))) t := by
    convert! ((((hasDerivAt_id t).const_mul A).add
      (((hasDerivAt_id t).pow 2).const_mul B |>.div_const 2)).sub
      (((hasDerivAt_id t).pow 3).const_mul C |>.div_const 3)).add
      (((hasDerivAt_id t).pow 4).const_mul (h ^ 2) |>.div_const 4) using 1
    simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    dsimp [A, B, C]
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (show IntervalIntegrable (fun t : ℝ => (1 - t) * ((q + t * h) * (1 - (q + t * h)))) volume 0 1 from
      (by apply Continuous.intervalIntegrable; fun_prop))
  rw [he]
  dsimp [F, A, B, C]
  ring

theorem reciprocal_tangent {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    2 / a - x / a ^ 2 ≤ 1 / x := by
  apply (le_div_iff₀ hx).mpr
  apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos ha)).mp
  have he := sq_nonneg (x - a)
  field_simp
  nlinarith

/-- The refined Jensen denominator is the actual weighted average variance. -/
theorem divergence_lower {q h : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hp : q + h ∈ Ioo (0 : ℝ) 1) :
    h ^ 2 / (2 * (q * (1 - q) + (1 - 2 * q) * h / 3 - h ^ 2 / 6)) ≤
      divergence q (q + h) := by
  let a := q * (1 - q) + (1 - 2 * q) * h / 3 - h ^ 2 / 6
  have ha : 0 < a := by
    have hv := mul_pos hq.1 (sub_pos.mpr hq.2)
    have hw := mul_pos hp.1 (sub_pos.mpr hp.2)
    dsimp [a]
    nlinarith [sq_nonneg h]
  let den : ℝ → ℝ := fun t => (q + t * h) * (1 - (q + t * h))
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 < den t := by
    have hm := path_mem hq hp ht
    exact mul_pos hm.1 (sub_pos.mpr hm.2)
  have hc : ContinuousOn (fun t : ℝ => h ^ 2 * (1 - t) / den t) (Icc 0 1) :=
    ContinuousOn.div (by fun_prop) (by dsimp [den]; fun_prop)
      (fun t ht => (hd t ht).ne')
  have hlc : Continuous (fun t : ℝ => h ^ 2 * (1 - t) * (2 / a - den t / a ^ 2)) := by
    dsimp [den]
    fun_prop
  have hle : (∫ t in (0 : ℝ)..1, h ^ 2 * (1 - t) * (2 / a - den t / a ^ 2)) ≤
      ∫ t in (0 : ℝ)..1, h ^ 2 * (1 - t) / den t := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (hlc.intervalIntegrable _ _) (hc.intervalIntegrable_of_Icc (by norm_num))
    intro t ht
    have he := mul_le_mul_of_nonneg_left (reciprocal_tangent (hd t ht) ha)
      (show 0 ≤ h ^ 2 * (1 - t) by exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr ht.2))
    simpa only [mul_one_div] using he
  have hfun : (fun t : ℝ => h ^ 2 * (1 - t) * (2 / a - den t / a ^ 2)) =
      (fun t : ℝ => (2 * h ^ 2 / a) * (1 - t) -
        (h ^ 2 / a ^ 2) * ((1 - t) * den t)) := by
    funext t
    ring
  have hleft : (∫ t in (0 : ℝ)..1, h ^ 2 * (1 - t) * (2 / a - den t / a ^ 2)) =
      h ^ 2 / (2 * a) := by
    rw [hfun, intervalIntegral.integral_sub
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; dsimp [den]; fun_prop),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hone : (∫ t in (0 : ℝ)..1, (1 - t)) = 1 / 2 := by
      have hd1 (t : ℝ) : HasDerivAt (fun x : ℝ => x - x ^ 2 / 2) (1 - t) t := by
        convert! (hasDerivAt_id t).sub (((hasDerivAt_id t).pow 2).div_const 2) using 1
        simp
      have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd1 t)
        (show IntervalIntegrable (fun t : ℝ => 1 - t) volume 0 1 from
          (by apply Continuous.intervalIntegrable; fun_prop))
      norm_num at he ⊢
      exact he
    rw [hone, show (∫ t in (0 : ℝ)..1, (1 - t) * den t) = a / 2 from
      weighted_variance_integral q h]
    field_simp
    ring
  rw [hleft] at hle
  rw [divergence_integral hq hp]
  exact hle

theorem divergence_lower_asymmetry {q h η : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hp : q + h ∈ Ioo (0 : ℝ) 1) (hη : |1 - 2 * q| ≤ η) :
    h ^ 2 / (2 * (q * (1 - q) + η * |h| / 3)) ≤ divergence q (q + h) := by
  have ha : 0 < q * (1 - q) + (1 - 2 * q) * h / 3 - h ^ 2 / 6 := by
    have hv := mul_pos hq.1 (sub_pos.mpr hq.2)
    have hw := mul_pos hp.1 (sub_pos.mpr hp.2)
    nlinarith [sq_nonneg h]
  have hh : (1 - 2 * q) * h ≤ η * |h| :=
    (le_abs_self _).trans ((abs_mul _ _).le.trans
      (mul_le_mul_of_nonneg_right hη (abs_nonneg h)))
  have hden : 2 * (q * (1 - q) + (1 - 2 * q) * h / 3 - h ^ 2 / 6) ≤
      2 * (q * (1 - q) + η * |h| / 3) := by nlinarith [sq_nonneg h]
  exact (div_le_div_of_nonneg_left (sq_nonneg h) (by linarith) hden).trans
    (divergence_lower hq hp)

#print axioms divergence_integral
#print axioms divergence_lower
#print axioms divergence_lower_asymmetry
end ForestUnimodality.BernoulliEntropy
