import ForestUnimodality.PointMassBudgetMonotonicity

/-! Exact square-root expressions for the point-mass costs, suitable for the
rational interval AST without an unverified real-power evaluation. -/
namespace ForestUnimodality.PointMassSqrtNormalization
open Real PointMassErrorEnvelope PointMassBudgetMonotonicity

theorem rpow_three_halves {x : ℝ} (hx : 0 < x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [show (3 / 2 : ℝ) = (1 : ℕ) + (1 / 2 : ℝ) by norm_num,
    Real.rpow_add hx, Real.rpow_natCast, pow_one, ← Real.sqrt_eq_rpow]

theorem rpow_neg_three_halves {x : ℝ} (hx : 0 < x) :
    x ^ (-(3 / 2 : ℝ)) = 1 / (x * Real.sqrt x) := by
  rw [Real.rpow_neg hx.le, rpow_three_halves hx, one_div]

theorem rpow_five_halves {x : ℝ} (hx : 0 < x) :
    x ^ (5 / 2 : ℝ) = x ^ 2 * Real.sqrt x := by
  rw [show (5 / 2 : ℝ) = (2 : ℕ) + (1 / 2 : ℝ) by norm_num,
    Real.rpow_add hx, Real.rpow_natCast, ← Real.sqrt_eq_rpow]

theorem coefficient_one {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1) :
    NegativePowerHermite.coefficient 1 alpha = 1 / alpha := by
  unfold NegativePowerHermite.coefficient
  rw [Real.rpow_neg_one]
  have hne : 1 - alpha ≠ 0 := by linarith
  field_simp
  ring

noncomputable def bThreeHalves (alpha : ℝ) : ℝ :=
  (1 / (alpha * Real.sqrt alpha) - 1 + (3 / 2) * (alpha - 1)) / (1 - alpha) ^ 2

theorem coefficient_threeHalves {alpha : ℝ} (ha : 0 < alpha) :
    NegativePowerHermite.coefficient (3 / 2) alpha = bThreeHalves alpha := by
  unfold NegativePowerHermite.coefficient bThreeHalves
  rw [rpow_neg_three_halves ha]

noncomputable def sqrtExpression (alpha v eta T D m : ℝ) : ℝ :=
  eta * rho alpha m ^ 2 / (3 * Real.pi * v * Real.sqrt m) *
      (1 + D / (alpha * m)) +
    (rho alpha m ^ 2 * Real.sqrt (rho alpha m)) /
      (16 * Real.sqrt (2 * Real.pi) * v * Real.sqrt v * m) *
        (1 + bThreeHalves alpha * D / m) +
    Real.sqrt m * (1 - T / Real.pi) * Real.exp (-v * alpha * m * T ^ 2 / 2) +
    Real.exp (-v * alpha * m * T ^ 2 / 2) /
      (Real.pi * v * alpha * T * Real.sqrt m)

theorem first_summand_eq {alpha m v eta D : ℝ}
    (hm : 0 < m) (ha : 0 < alpha) (ha1 : alpha < 1) (hv : 0 < v) :
    (Real.sqrt m * costOne alpha m v eta) * momentFactor 1 alpha D m =
      eta * rho alpha m ^ 2 / (3 * Real.pi * v * Real.sqrt m) *
        (1 + D / (alpha * m)) := by
  rw [sqrt_mul_costOne hm hv]
  unfold momentFactor
  rw [coefficient_one ha ha1]
  field_simp

theorem second_summand_eq {alpha m v D : ℝ}
    (hm : 0 < m) (ha : 0 < alpha) (ham : 1 < alpha * m) (hv : 0 < v) :
    (Real.sqrt m * costThreeHalves alpha m v) * momentFactor (3 / 2) alpha D m =
      (rho alpha m ^ 2 * Real.sqrt (rho alpha m)) /
        (16 * Real.sqrt (2 * Real.pi) * v * Real.sqrt v * m) *
          (1 + bThreeHalves alpha * D / m) := by
  rw [sqrt_mul_costThreeHalves hm hv, rpow_five_halves (rho_pos ham),
    rpow_three_halves hv]
  unfold momentFactor
  rw [coefficient_threeHalves ha]
  ring

theorem tail_summands_eq {alpha m v T : ℝ}
    (hm : 0 < m) (ha : 0 < alpha) (hv : 0 < v) (hT : 0 < T) :
    Real.sqrt m * tailCost alpha m v T =
      Real.sqrt m * (1 - T / Real.pi) * Real.exp (-v * alpha * m * T ^ 2 / 2) +
      Real.exp (-v * alpha * m * T ^ 2 / 2) /
        (Real.pi * v * alpha * T * Real.sqrt m) := by
  have hs : Real.sqrt m ≠ 0 := (Real.sqrt_pos.mpr hm).ne'
  unfold tailCost
  rw [show -v * (alpha * m) * T ^ 2 / 2 = -v * alpha * m * T ^ 2 / 2 by ring]
  field_simp [hm.ne', ha.ne', hv.ne', hT.ne', hs, Real.pi_ne_zero]
  rw [Real.sq_sqrt hm.le]
  ring

theorem scaledError_eq_sqrtExpression {alpha m v eta T D : ℝ}
    (hm : 0 < m) (ha : 0 < alpha) (ha1 : alpha < 1)
    (ham : 1 < alpha * m) (hv : 0 < v) (hT : 0 < T) :
    scaledError alpha v eta T D m = sqrtExpression alpha v eta T D m := by
  unfold scaledError
  rw [mul_add, mul_add, ← mul_assoc (Real.sqrt m) (costOne alpha m v eta),
    ← mul_assoc (Real.sqrt m) (costThreeHalves alpha m v),
    first_summand_eq hm ha ha1 hv, second_summand_eq hm ha ham hv,
    tail_summands_eq hm ha hv hT]
  unfold sqrtExpression
  ring

#print axioms coefficient_one
#print axioms coefficient_threeHalves
#print axioms scaledError_eq_sqrtExpression
end ForestUnimodality.PointMassSqrtNormalization
