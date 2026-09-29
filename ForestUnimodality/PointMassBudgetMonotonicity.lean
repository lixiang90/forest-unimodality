import ForestUnimodality.PointMassErrorEnvelope
import ForestUnimodality.NegativePowerHermite
import ForestUnimodality.UnboundedBudget

/-! Infinite-scale continuation of the actual stage-900 point-mass prices. -/
namespace ForestUnimodality.PointMassBudgetMonotonicity
open Real Set PointMassErrorEnvelope

noncomputable def momentFactor (p alpha D m : ℝ) : ℝ :=
  1 + NegativePowerHermite.coefficient p alpha * D / m

noncomputable def mainBracket (R D rate m : ℝ) : ℝ :=
  Real.exp (-R / 2 - 3 * D / (2 * m)) - (43 / 40) * Real.exp (-rate * m)

noncomputable def scaledError (alpha vminus eta T D m : ℝ) : ℝ :=
  Real.sqrt m * (costOne alpha m vminus eta * momentFactor 1 alpha D m +
    costThreeHalves alpha m vminus * momentFactor (3 / 2) alpha D m +
    tailCost alpha m vminus T)

theorem coefficient_nonneg {p alpha : ℝ} (hp : 0 ≤ p) (ha : 0 < alpha) :
    0 ≤ NegativePowerHermite.coefficient p alpha := by
  have hi : 0 ≤ NegativePowerHermite.integralCoefficient p alpha := by
    unfold NegativePowerHermite.integralCoefficient
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro s hs
    have hb : 0 < 1 + s * (alpha - 1) := by
      by_cases hh : 1 ≤ alpha
      · nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hh)]
      · nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr (le_of_not_ge hh))]
    have hsp : 0 ≤ 1 - s := sub_nonneg.mpr hs.2
    positivity
  have hid := NegativePowerHermite.integralCoefficient_identity p ha
  unfold NegativePowerHermite.coefficient
  apply div_nonneg _ (sq_nonneg _)
  rw [← hid]
  exact mul_nonneg (sq_nonneg _) hi

theorem momentFactor_nonneg {p alpha D m : ℝ}
    (hp : 0 ≤ p) (ha : 0 < alpha) (hD : 0 ≤ D) (hm : 0 < m) :
    0 ≤ momentFactor p alpha D m := by
  have hc := coefficient_nonneg hp ha
  unfold momentFactor
  positivity

theorem momentFactor_antitone {p alpha D x y : ℝ}
    (hp : 0 ≤ p) (ha : 0 < alpha) (hD : 0 ≤ D) (hx : 0 < x) (hxy : x ≤ y) :
    momentFactor p alpha D y ≤ momentFactor p alpha D x := by
  have hc := coefficient_nonneg hp ha
  unfold momentFactor
  exact add_le_add le_rfl (div_le_div_of_nonneg_left (mul_nonneg hc hD) hx hxy)

theorem mainBracket_monotoneOn {R D rate start : ℝ}
    (hs : 0 < start) (hD : 0 ≤ D) (hrate : 0 ≤ rate) :
    MonotoneOn (mainBracket R D rate) (Ici start) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := hs.trans_le hx
  have hfrac : 3 * D / (2 * y) ≤ 3 * D / (2 * x) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  unfold mainBracket
  apply sub_le_sub
  · exact Real.exp_le_exp.mpr (by linarith)
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hxy hrate]

theorem sqrt_mul_costOne {alpha m vminus eta : ℝ}
    (hm : 0 < m) (hv : 0 < vminus) :
    Real.sqrt m * costOne alpha m vminus eta =
      eta / (3 * Real.pi * vminus) * (rho alpha m ^ 2 / Real.sqrt m) := by
  have hs : Real.sqrt m ≠ 0 := (Real.sqrt_pos.mpr hm).ne'
  unfold costOne
  field_simp [hm.ne', hv.ne', hs, Real.pi_ne_zero]
  rw [Real.sq_sqrt hm.le]
  ring

private theorem rpow_three_halves {x : ℝ} (hx : 0 < x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [show (3 / 2 : ℝ) = (1 : ℕ) + (1 / 2 : ℝ) by norm_num,
    Real.rpow_add hx, Real.rpow_natCast, pow_one, ← Real.sqrt_eq_rpow]

theorem sqrt_mul_costThreeHalves {alpha m vminus : ℝ}
    (hm : 0 < m) (hv : 0 < vminus) :
    Real.sqrt m * costThreeHalves alpha m vminus =
      (1 / (16 * Real.sqrt (2 * Real.pi) * vminus ^ (3 / 2 : ℝ))) *
        (rho alpha m ^ (5 / 2 : ℝ) / m) := by
  have hs : Real.sqrt m ≠ 0 := (Real.sqrt_pos.mpr hm).ne'
  unfold costThreeHalves
  rw [Real.mul_rpow hv.le hm.le, rpow_three_halves hm]
  field_simp

theorem sqrt_mul_costOne_antitone {alpha vminus eta x y : ℝ}
    (ha : 0 < alpha) (hv : 0 < vminus) (heta : 0 ≤ eta)
    (hx : 0 < x) (hax : 1 < alpha * x) (hxy : x ≤ y) :
    Real.sqrt y * costOne alpha y vminus eta ≤
      Real.sqrt x * costOne alpha x vminus eta := by
  have hy := hx.trans_le hxy
  have hay : 1 < alpha * y := hax.trans_le (mul_le_mul_of_nonneg_left hxy ha.le)
  have hr := UnboundedBudget.bridgeRatio_antitone ha hax hxy
  change rho alpha y ≤ rho alpha x at hr
  rw [sqrt_mul_costOne hy hv, sqrt_mul_costOne hx hv]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact div_le_div₀ (sq_nonneg _) (pow_le_pow_left₀ (rho_pos hay).le hr 2)
    (Real.sqrt_pos.mpr hx) (Real.sqrt_le_sqrt hxy)

theorem sqrt_mul_costThreeHalves_antitone {alpha vminus x y : ℝ}
    (ha : 0 < alpha) (hv : 0 < vminus)
    (hx : 0 < x) (hax : 1 < alpha * x) (hxy : x ≤ y) :
    Real.sqrt y * costThreeHalves alpha y vminus ≤
      Real.sqrt x * costThreeHalves alpha x vminus := by
  have hy := hx.trans_le hxy
  have hay : 1 < alpha * y := hax.trans_le (mul_le_mul_of_nonneg_left hxy ha.le)
  have hr := UnboundedBudget.bridgeRatio_antitone ha hax hxy
  change rho alpha y ≤ rho alpha x at hr
  rw [sqrt_mul_costThreeHalves hy hv, sqrt_mul_costThreeHalves hx hv]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hrx := rho_pos hax
  exact div_le_div₀ (by positivity)
    (Real.rpow_le_rpow (rho_pos hay).le hr (by norm_num)) hx hxy

theorem sqrt_mul_tailCost_eq {alpha m vminus T : ℝ}
    (hm : 0 < m) (ha : 0 < alpha) (hv : 0 < vminus) (hT : 0 < T) :
    Real.sqrt m * tailCost alpha m vminus T =
      (1 - T / Real.pi) * UnboundedBudget.powerExpCost (1 / 2)
        (vminus * alpha * T ^ 2 / 2) m +
      (1 / (Real.pi * vminus * alpha * T)) * UnboundedBudget.powerExpCost (-1 / 2)
        (vminus * alpha * T ^ 2 / 2) m := by
  have hs : Real.sqrt m ≠ 0 := (Real.sqrt_pos.mpr hm).ne'
  unfold tailCost UnboundedBudget.powerExpCost
  rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hm.le,
    ← Real.sqrt_eq_rpow]
  have he : -vminus * (alpha * m) * T ^ 2 / 2 = -(vminus * alpha * T ^ 2 / 2) * m := by ring
  rw [he]
  field_simp [hm.ne', ha.ne', hv.ne', hT.ne', hs, Real.pi_ne_zero]
  rw [Real.sq_sqrt hm.le]
  ring

theorem sqrt_mul_tailCost_antitoneOn {alpha vminus T start : ℝ}
    (hs : 0 < start) (ha : 0 < alpha) (hv : 0 < vminus)
    (hT : 0 < T) (hTpi : T ≤ Real.pi)
    (hthreshold : 1 / 2 ≤ vminus * alpha * start * T ^ 2 / 2) :
    AntitoneOn (fun m => Real.sqrt m * tailCost alpha m vminus T) (Ici start) := by
  have hr : 0 ≤ vminus * alpha * T ^ 2 / 2 := by positivity
  have hth : (1 / 2 : ℝ) ≤ (vminus * alpha * T ^ 2 / 2) * start := by nlinarith
  have hfirst := UnboundedBudget.powerExpCost_antitoneOn hs hr hth
  have hsecond := UnboundedBudget.powerExpCost_antitoneOn hs hr
    (show (-1 / 2 : ℝ) ≤ (vminus * alpha * T ^ 2 / 2) * start by linarith)
  have hfactor : 0 ≤ 1 - T / Real.pi := by
    have := (div_le_one Real.pi_pos).mpr hTpi
    linarith
  intro x hx y hy hxy
  dsimp only
  rw [sqrt_mul_tailCost_eq (hs.trans_le hy) ha hv hT,
    sqrt_mul_tailCost_eq (hs.trans_le hx) ha hv hT]
  exact add_le_add (mul_le_mul_of_nonneg_left (hfirst hx hy hxy) hfactor)
    (mul_le_mul_of_nonneg_left (hsecond hx hy hxy) (by positivity))

theorem scaledError_antitoneOn {alpha vminus eta T D start : ℝ}
    (hs : 0 < start) (ha : 0 < alpha) (has : 1 < alpha * start)
    (hv : 0 < vminus) (heta : 0 ≤ eta) (hD : 0 ≤ D)
    (hT : 0 < T) (hTpi : T ≤ Real.pi)
    (hthreshold : 1 / 2 ≤ vminus * alpha * start * T ^ 2 / 2) :
    AntitoneOn (scaledError alpha vminus eta T D) (Ici start) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := hs.trans_le hx
  have hy0 : 0 < y := hs.trans_le hy
  have hax : 1 < alpha * x := has.trans_le (mul_le_mul_of_nonneg_left hx ha.le)
  have hay : 1 < alpha * y := has.trans_le (mul_le_mul_of_nonneg_left hy ha.le)
  have h1 := sqrt_mul_costOne_antitone ha hv heta hx0 hax hxy
  have h32 := sqrt_mul_costThreeHalves_antitone ha hv hx0 hax hxy
  have hj1 := momentFactor_antitone (p := 1) (by norm_num) ha hD hx0 hxy
  have hj32 := momentFactor_antitone (p := 3/2) (by norm_num) ha hD hx0 hxy
  have he1 := mul_le_mul h1 hj1
    (momentFactor_nonneg (by norm_num) ha hD hy0)
    (mul_nonneg (Real.sqrt_nonneg x) (costOne_nonneg hx0.le hv.le heta))
  have he32 := mul_le_mul h32 hj32
    (momentFactor_nonneg (by norm_num) ha hD hy0)
    (mul_nonneg (Real.sqrt_nonneg x) (costThreeHalves_nonneg hx0 hax hv))
  have ht := sqrt_mul_tailCost_antitoneOn hs ha hv hT hTpi hthreshold hx hy hxy
  simpa only [scaledError, mul_add, mul_assoc] using add_le_add (add_le_add he1 he32) ht

noncomputable def budget (H R D rate alpha vminus eta T m : ℝ) : ℝ :=
  H * mainBracket R D rate m - scaledError alpha vminus eta T D m

theorem budget_monotoneOn {H R D rate alpha vminus eta T start : ℝ}
    (hH : 0 ≤ H) (hs : 0 < start) (ha : 0 < alpha) (has : 1 < alpha * start)
    (hv : 0 < vminus) (heta : 0 ≤ eta) (hD : 0 ≤ D) (hrate : 0 ≤ rate)
    (hT : 0 < T) (hTpi : T ≤ Real.pi)
    (hthreshold : 1 / 2 ≤ vminus * alpha * start * T ^ 2 / 2) :
    MonotoneOn (budget H R D rate alpha vminus eta T) (Ici start) := by
  intro x hx y hy hxy
  exact sub_le_sub
    (mul_le_mul_of_nonneg_left (mainBracket_monotoneOn hs hD hrate hx hy hxy) hH)
    (scaledError_antitoneOn hs ha has hv heta hD hT hTpi hthreshold hx hy hxy)

theorem budget_pos_of_start {H R D rate alpha vminus eta T start m : ℝ}
    (hH : 0 ≤ H) (hs : 0 < start) (ha : 0 < alpha) (has : 1 < alpha * start)
    (hv : 0 < vminus) (heta : 0 ≤ eta) (hD : 0 ≤ D) (hrate : 0 ≤ rate)
    (hT : 0 < T) (hTpi : T ≤ Real.pi)
    (hthreshold : 1 / 2 ≤ vminus * alpha * start * T ^ 2 / 2)
    (hpositive : 0 < budget H R D rate alpha vminus eta T start) (hm : start ≤ m) :
    0 < budget H R D rate alpha vminus eta T m :=
  hpositive.trans_le (budget_monotoneOn hH hs ha has hv heta hD hrate hT hTpi hthreshold
    (by simp) hm hm)

#print axioms coefficient_nonneg
#print axioms mainBracket_monotoneOn
#print axioms sqrt_mul_tailCost_antitoneOn
#print axioms scaledError_antitoneOn
#print axioms budget_pos_of_start
end ForestUnimodality.PointMassBudgetMonotonicity
