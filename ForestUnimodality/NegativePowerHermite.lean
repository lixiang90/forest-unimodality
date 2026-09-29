import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! A real-domain Hermite upper envelope for every negative power.
The integral coefficient provides both the remainder sign and the
monotonicity needed by cumulative lower-tail charges. -/
namespace ForestUnimodality.NegativePowerHermite
open Set Real MeasureTheory

noncomputable def coefficient (p beta : ℝ) : ℝ :=
  (beta ^ (-p) - 1 + p * (beta - 1)) / (1 - beta) ^ 2

noncomputable def envelope (p beta y : ℝ) : ℝ :=
  1 - p * (y - 1) + coefficient p beta * (y - 1) ^ 2

noncomputable def integralCoefficient (p y : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, (1 - s) * p * (p + 1) * (1 + s * (y - 1)) ^ (-p - 2)

private theorem affine_pos {y s : ℝ} (hy : 0 < y) (hs : s ∈ Icc 0 1) :
    0 < 1 + s * (y - 1) := by
  by_cases h : 1 ≤ y
  · have hm := mul_nonneg hs.1 (sub_nonneg.mpr h)
    linarith
  · have hm := mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr (le_of_not_ge h))
    nlinarith

private theorem coefficient_integrand_continuous (p : ℝ) {y : ℝ} (hy : 0 < y) :
    ContinuousOn (fun s : ℝ => (1 - s) * p * (p + 1) *
      (1 + s * (y - 1)) ^ (-p - 2)) (Icc 0 1) := by
  apply ContinuousOn.mul (by fun_prop)
  exact (show ContinuousOn (fun s : ℝ => 1 + s * (y - 1)) (Icc 0 1) by fun_prop).rpow_const
    (fun s hs => Or.inl (affine_pos hy hs).ne')

/-- Exact remainder identity, including the repeated contact point y=1. -/
theorem integralCoefficient_identity (p : ℝ) {y : ℝ} (hy : 0 < y) :
    (y - 1) ^ 2 * integralCoefficient p y = y ^ (-p) - 1 + p * (y - 1) := by
  let F : ℝ → ℝ := fun s =>
    (1 - s) * (-p * (y - 1) * (1 + s * (y - 1)) ^ (-p - 1)) +
      (1 + s * (y - 1)) ^ (-p)
  have hd (s : ℝ) (hs : s ∈ Icc 0 1) : HasDerivAt F
      ((y - 1) ^ 2 * ((1 - s) * p * (p + 1) * (1 + s * (y - 1)) ^ (-p - 2))) s := by
    have hz : 1 + s * (y - 1) ≠ 0 := (affine_pos hy hs).ne'
    have hlin : HasDerivAt (fun t : ℝ => 1 + t * (y - 1)) (y - 1) s := by
      convert! ((hasDerivAt_id s).mul_const (y - 1)).const_add 1 using 1
      simp
    have h0 := hlin.rpow_const (p := -p) (Or.inl hz)
    have h1 := hlin.rpow_const (p := -p - 1) (Or.inl hz)
    have hD := (((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).mul
      (h1.const_mul (-p * (y - 1)))).add h0
    convert! hD using 1
    simp only [Pi.sub_apply, id_eq]
    rw [show -p - 1 - 1 = -p - 2 by ring]
    ring
  have hint : IntervalIntegrable (fun s : ℝ => (y - 1) ^ 2 *
      ((1 - s) * p * (p + 1) * (1 + s * (y - 1)) ^ (-p - 2))) volume 0 1 :=
    (coefficient_integrand_continuous p hy).intervalIntegrable_of_Icc (by norm_num) |>.const_mul _
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hd s (by simpa using hs)) hint
  rw [intervalIntegral.integral_const_mul] at he
  dsimp only [F] at he
  simp at he
  dsimp [integralCoefficient]
  linarith

theorem integralCoefficient_antitone {p : ℝ} (hp : 0 < p) :
    AntitoneOn (integralCoefficient p) (Ioi 0) := by
  intro x hx y hy hxy
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((coefficient_integrand_continuous p hy).intervalIntegrable_of_Icc (by norm_num))
    ((coefficient_integrand_continuous p hx).intervalIntegrable_of_Icc (by norm_num))
  intro s hs
  apply mul_le_mul_of_nonneg_left
  · apply Real.rpow_le_rpow_of_nonpos (affine_pos hx hs)
    · nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hxy)]
    · linarith
  · exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hs.2) hp.le) (by linarith)

theorem integralCoefficient_one (p : ℝ) : integralCoefficient p 1 = p * (p + 1) / 2 := by
  unfold integralCoefficient
  simp only [sub_self, mul_zero, add_zero, Real.one_rpow, mul_one]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
  have hi : (∫ s : ℝ in (0 : ℝ)..1, 1 - s) = 1 / 2 := by
    rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun s : ℝ => s)
      (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _)]
    norm_num
  rw [hi]
  ring

theorem coefficient_eq_integralCoefficient (p : ℝ) {beta : ℝ}
    (hb : 0 < beta) (hb1 : beta < 1) : coefficient p beta = integralCoefficient p beta := by
  unfold coefficient
  apply (div_eq_iff (pow_ne_zero 2 (by linarith : 1 - beta ≠ 0))).mpr
  have he := integralCoefficient_identity p hb
  nlinarith

theorem coefficient_lower {p beta : ℝ} (hp : 0 < p) (hb : 0 < beta) (hb1 : beta < 1) :
    p * (p + 1) / 2 ≤ coefficient p beta := by
  rw [coefficient_eq_integralCoefficient p hb hb1, ← integralCoefficient_one]
  exact integralCoefficient_antitone hp hb (by norm_num) hb1.le

theorem coefficient_gt_quarter_sq {p beta : ℝ}
    (hp : 0 < p) (hb : 0 < beta) (hb1 : beta < 1) :
    p ^ 2 / 4 < coefficient p beta := by
  have hl := coefficient_lower hp hb hb1
  nlinarith [sq_nonneg p]

/-- The same quadratic used on the good event is positive on the entire
real line, including the part discarded as a bad event. -/
theorem envelope_pos {p beta : ℝ} (hp : 0 < p) (hb : 0 < beta) (hb1 : beta < 1)
    (y : ℝ) : 0 < envelope p beta y := by
  have hB := coefficient_gt_quarter_sq hp hb hb1
  have hB0 : 0 ≤ 4 * coefficient p beta := by nlinarith [sq_nonneg p]
  have he : 4 * coefficient p beta * envelope p beta y =
      (2 * coefficient p beta * (y - 1) - p) ^ 2 + 4 * coefficient p beta - p ^ 2 := by
    unfold envelope
    ring
  by_contra hnot
  have hn := mul_nonpos_of_nonneg_of_nonpos hB0 (le_of_not_gt hnot)
  rw [he] at hn
  nlinarith [sq_nonneg (2 * coefficient p beta * (y - 1) - p)]

theorem gap_identity (p : ℝ) {beta y : ℝ} (hb : 0 < beta) (hb1 : beta < 1) (hy : 0 < y) :
    y ^ (-p) - envelope p beta y =
      (integralCoefficient p y - integralCoefficient p beta) * (y - 1) ^ 2 := by
  unfold envelope
  rw [coefficient_eq_integralCoefficient p hb hb1]
  have he := integralCoefficient_identity p hy
  nlinarith

/-- The true negative-power function is bounded by its Hermite quadratic
on the whole unbounded interval y >= beta. -/
theorem rpow_le_envelope {p beta y : ℝ}
    (hp : 0 < p) (hb : 0 < beta) (hb1 : beta < 1) (hy : beta ≤ y) :
    y ^ (-p) ≤ envelope p beta y := by
  have hy0 : 0 < y := hb.trans_le hy
  have hc := integralCoefficient_antitone hp hb hy0 hy
  have hg := gap_identity p hb hb1 hy0
  have hm := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hc) (sq_nonneg (y - 1))
  linarith

theorem gap_nonneg {p beta y : ℝ}
    (hp : 0 < p) (hb : 0 < beta) (hb1 : beta < 1) (hy : 0 < y) (hyb : y ≤ beta) :
    0 ≤ y ^ (-p) - envelope p beta y := by
  rw [gap_identity p hb hb1 hy]
  exact mul_nonneg (sub_nonneg.mpr (integralCoefficient_antitone hp hy hb hyb)) (sq_nonneg _)

/-- The actual missing amount decreases continuously along the lower
tail. It is not inferred from a finite collection of sampled nodes. -/
theorem gap_antitone {p beta : ℝ} (hp : 0 < p) (hb : 0 < beta) (hb1 : beta < 1) :
    AntitoneOn (fun y : ℝ => y ^ (-p) - envelope p beta y) (Ioc 0 beta) := by
  intro x hx y hy hxy
  dsimp only
  rw [gap_identity p hb hb1 hy.1, gap_identity p hb hb1 hx.1]
  have hcoef : integralCoefficient p y - integralCoefficient p beta ≤
      integralCoefficient p x - integralCoefficient p beta :=
    sub_le_sub_right (integralCoefficient_antitone hp hx.1 hy.1 hxy) _
  have hsquare : (y - 1) ^ 2 ≤ (x - 1) ^ 2 := by
    have hy1 : y ≤ 1 := hy.2.trans hb1.le
    nlinarith
  exact mul_le_mul hcoef hsquare (sq_nonneg (y - 1))
    (sub_nonneg.mpr (integralCoefficient_antitone hp hx.1 hb hx.2))

noncomputable def positiveGap (p beta y : ℝ) : ℝ := max 0 (y ^ (-p) - envelope p beta y)

theorem positiveGap_antitone {p beta : ℝ} (hp : 0 < p) (hb : 0 < beta) (hb1 : beta < 1) :
    AntitoneOn (positiveGap p beta) (Ioc 0 beta) := by
  intro x hx y hy hxy
  exact max_le_max le_rfl (gap_antitone hp hb hb1 hx hy hxy)

theorem positiveGap_zero_of_ge {p beta y : ℝ}
    (hp : 0 < p) (hb : 0 < beta) (hb1 : beta < 1) (hy : beta ≤ y) :
    positiveGap p beta y = 0 := by
  exact max_eq_left (sub_nonpos.mpr (rpow_le_envelope hp hb hb1 hy))

theorem positiveGap_antitoneOn_interval {p alpha beta : ℝ}
    (hp : 0 < p) (ha : 0 < alpha) (hab : alpha < beta) (hb1 : beta < 1) :
    AntitoneOn (positiveGap p beta) (Icc alpha beta) := by
  exact (positiveGap_antitone hp (ha.trans hab) hb1).mono
    (fun y hy => ⟨ha.trans_le hy.1, hy.2⟩)

#print axioms integralCoefficient_identity
#print axioms integralCoefficient_antitone
#print axioms coefficient_lower
#print axioms envelope_pos
#print axioms rpow_le_envelope
#print axioms positiveGap_antitone
end ForestUnimodality.NegativePowerHermite
