import ForestUnimodality.ShortLegFinite

namespace ForestUnimodality.ShortLegData
open MeanTerminalClosure

/-- The same numerator for a real host ratio; arithmetic certificates only
fix the rational endpoints, and the following proof covers the interval. -/
noncomputable def residualReal (odd : Bool) (legs : List ℕ) (delta : ℕ) (r : ℝ) : ℝ :=
  let h : ℝ := 29 / 60 + if odd then 0 else delta
  ((legs.map ratio).prod : ℝ) * (((legs.map excess).sum : ℝ) - h) +
    (r - 1) * ((legs.map deletedExcess).sum : ℝ) + h + if odd then r * delta else 0

theorem residual_cast (odd : Bool) (legs : List ℕ) (delta : ℕ) (r : ℚ) :
    (residual odd legs delta r : ℝ) = residualReal odd legs delta r := by
  cases odd <;> simp [residual, residualReal]

theorem residualReal_affine (odd : Bool) (legs : List ℕ) (delta : ℕ) (r : ℝ) :
    residualReal odd legs delta r = residualReal odd legs delta 1 +
      (r - 1) * (((legs.map deletedExcess).sum : ℝ) + if odd then delta else 0) := by
  cases odd <;> simp only [residualReal, Bool.false_eq_true, ↓reduceIte] <;> ring

theorem residualReal_pos_of_endpoints (odd : Bool) (legs : List ℕ) (delta : ℕ)
    (h1 : 0 < residual odd legs delta 1) (h3 : 0 < residual odd legs delta 3)
    (r : ℝ) (hr1 : 1 ≤ r) (hr3 : r ≤ 3) : 0 < residualReal odd legs delta r := by
  have hl : 0 < residualReal odd legs delta 1 := by
    simpa only [residual_cast, Rat.cast_one] using (Rat.cast_pos (K := ℝ)).mpr h1
  have hh : 0 < residualReal odd legs delta 3 := by
    simpa only [residual_cast, Rat.cast_ofNat] using (Rat.cast_pos (K := ℝ)).mpr h3
  let d : ℝ := ((legs.map deletedExcess).sum : ℝ) + if odd then delta else 0
  have he := residualReal_affine odd legs delta r
  have he3 := residualReal_affine odd legs delta 3
  change residualReal odd legs delta r = residualReal odd legs delta 1 + (r - 1) * d at he
  change residualReal odd legs delta 3 = residualReal odd legs delta 1 + (3 - 1) * d at he3
  by_cases hd : 0 ≤ d
  · have hmul := mul_nonneg (sub_nonneg.mpr hr1) hd
    linarith
  · have hmul := mul_le_mul_of_nonpos_right (show r - 1 ≤ 3 - 1 by linarith) (le_of_not_ge hd)
    linarith

theorem finite_leg_real_positive (odd : Bool) (fan : List ℕ) (delta : ℕ)
    (hm : fan.length = 2 ∨ fan.length = 3)
    (hdesc : DescendingBounded (legBound odd) fan) (hd : delta ≤ 1)
    (he : exceptional odd (legsOf odd fan) delta = false)
    (r : ℝ) (hr1 : 1 ≤ r) (hr3 : r ≤ 3) :
    0 < residualReal odd (legsOf odd fan) delta r := by
  have hc := finite_leg_classification odd fan delta hm hdesc hd
  simp only [he, Bool.false_eq_true, ↓reduceIte] at hc
  exact residualReal_pos_of_endpoints odd _ delta hc.1 hc.2 r hr1 hr3

#print axioms residualReal_pos_of_endpoints
#print axioms finite_leg_real_positive
end ForestUnimodality.ShortLegData
