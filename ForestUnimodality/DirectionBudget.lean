import ForestUnimodality.PointMassBudgetMonotonicity
import ForestUnimodality.GradientBudgetMonotonicity
import ForestUnimodality.ProbabilityDirectionBudget
import ForestUnimodality.PointMassLayerBudget
import ForestUnimodality.ReciprocalGradientBudget

/-! Fixed interval parameters for the mean-preserving direction estimate.
The endpoint-to-half-line step concerns the actual analytic expressions. -/
namespace ForestUnimodality.DirectionBudget
open Set

structure Parameters where
  a : ℝ
  b : ℝ
  start : ℝ
  alpha : ℝ
  alpha1 : ℝ
  vmin : ℝ
  vmax : ℝ
  eta : ℝ
  R : ℝ
  D : ℝ
  T : ℝ
  rate0 : ℝ
  rate1 : ℝ
  c0 : ℝ
  c1 : ℝ

noncomputable def Parameters.H (p : Parameters) : ℝ := 1 / Real.sqrt (2 * Real.pi * p.vmax)
noncomputable def Parameters.A0 (p : Parameters) : ℝ := p.c0 / (p.vmin * p.alpha)
noncomputable def Parameters.A1 (p : Parameters) : ℝ := p.c1 / (p.vmin * p.alpha1)
noncomputable def Parameters.mass (p : Parameters) (m : ℝ) : ℝ :=
  PointMassBudgetMonotonicity.budget p.H p.R p.D p.rate0 p.alpha p.vmin p.eta p.T m
noncomputable def Parameters.gradient (p : Parameters) (m : ℝ) : ℝ :=
  GradientBudgetMonotonicity.gradientCost (p.c0 / p.vmin) p.D p.alpha
    p.A0 p.A1 p.rate0 p.rate1 m
noncomputable def Parameters.leftMargin (p : Parameters) (m : ℝ) : ℝ :=
  (1 - p.b) * p.mass m - p.b * p.gradient m
noncomputable def Parameters.rightMargin (p : Parameters) (m : ℝ) : ℝ :=
  (p.a - 1) * p.mass m - p.gradient m

structure Parameters.Valid (p : Parameters) : Prop where
  start_pos : 0 < p.start
  alpha_pos : 0 < p.alpha
  alpha1_pos : 0 < p.alpha1
  alpha1_le : p.alpha1 ≤ p.alpha
  alpha_lt : p.alpha < 1
  cutoff_count : 1 < p.alpha * p.start
  vmin_pos : 0 < p.vmin
  vmax_pos : 0 < p.vmax
  eta_nonneg : 0 ≤ p.eta
  R_nonneg : 0 ≤ p.R
  D_nonneg : 0 ≤ p.D
  T_pos : 0 < p.T
  T_lt_pi : p.T < Real.pi
  rate0_nonneg : 0 ≤ p.rate0
  rate1_nonneg : 0 ≤ p.rate1
  c0_nonneg : 0 ≤ p.c0
  c1_nonneg : 0 ≤ p.c1
  price_order : p.A0 ≤ p.A1
  price_lt_start : p.A1 < p.start
  frequency_threshold : 1 / 2 ≤ p.vmin * p.alpha * p.T ^ 2 / 2 * p.start
  gradient_threshold : p.start + p.A1 ≤ 2 * p.rate1 * p.start * (p.start - p.A1)

theorem Parameters.Valid.mass_monotoneOn {p : Parameters} (h : p.Valid) :
    MonotoneOn p.mass (Ici p.start) := by
  apply PointMassBudgetMonotonicity.budget_monotoneOn
    (H := p.H) (R := p.R) (D := p.D) (rate := p.rate0) (alpha := p.alpha)
    (vminus := p.vmin) (eta := p.eta) (T := p.T)
    ?_ h.start_pos h.alpha_pos h.cutoff_count h.vmin_pos h.eta_nonneg h.D_nonneg
    h.rate0_nonneg h.T_pos h.T_lt_pi.le ?_
  · unfold Parameters.H
    positivity
  · nlinarith only [h.frequency_threshold]

theorem Parameters.Valid.gradient_antitoneOn {p : Parameters} (h : p.Valid) :
    AntitoneOn p.gradient (Ici p.start) :=
  GradientBudgetMonotonicity.gradientCost_antitoneOn
    (div_nonneg h.c0_nonneg h.vmin_pos.le) h.D_nonneg h.alpha_pos h.price_order
    (div_nonneg h.c1_nonneg (mul_pos h.vmin_pos h.alpha1_pos).le)
    h.price_lt_start h.rate0_nonneg h.rate1_nonneg h.gradient_threshold

theorem Parameters.Valid.leftMargin_monotoneOn {p : Parameters} (h : p.Valid)
    (hb0 : 0 ≤ p.b) (hb1 : p.b ≤ 1) : MonotoneOn p.leftMargin (Ici p.start) := by
  intro x hx y hy hxy
  exact sub_le_sub
    (mul_le_mul_of_nonneg_left (h.mass_monotoneOn hx hy hxy) (sub_nonneg.mpr hb1))
    (mul_le_mul_of_nonneg_left (h.gradient_antitoneOn hx hy hxy) hb0)

theorem Parameters.Valid.rightMargin_monotoneOn {p : Parameters} (h : p.Valid)
    (ha : 1 ≤ p.a) : MonotoneOn p.rightMargin (Ici p.start) := by
  intro x hx y hy hxy
  exact sub_le_sub
    (mul_le_mul_of_nonneg_left (h.mass_monotoneOn hx hy hxy) (sub_nonneg.mpr ha))
    (h.gradient_antitoneOn hx hy hxy)

theorem Parameters.Valid.leftMargin_positive {p : Parameters} (h : p.Valid)
    (hb0 : 0 ≤ p.b) (hb1 : p.b ≤ 1) (hstart : 0 < p.leftMargin p.start)
    {m : ℝ} (hm : p.start ≤ m) : 0 < p.leftMargin m :=
  hstart.trans_le (h.leftMargin_monotoneOn hb0 hb1 (by simp) hm hm)

theorem Parameters.Valid.rightMargin_positive {p : Parameters} (h : p.Valid)
    (ha : 1 ≤ p.a) (hstart : 0 < p.rightMargin p.start)
    {m : ℝ} (hm : p.start ≤ m) : 0 < p.rightMargin m :=
  hstart.trans_le (h.rightMargin_monotoneOn ha (by simp) hm hm)

#print axioms Parameters.Valid.mass_monotoneOn
#print axioms Parameters.Valid.leftMargin_positive
#print axioms Parameters.Valid.rightMargin_positive
end ForestUnimodality.DirectionBudget
