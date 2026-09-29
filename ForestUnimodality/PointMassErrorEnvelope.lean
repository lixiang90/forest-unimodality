import ForestUnimodality.BinomialPointMassError

/-! Fixed prices for the actual finite binomial point-mass error. Every price
uses the same lower cutoff `alpha * m` and variance lower bound. -/
namespace ForestUnimodality.PointMassErrorEnvelope
open Real

noncomputable def rho (alpha m : ℝ) : ℝ := alpha * m / (alpha * m - 1)

noncomputable def costOne (alpha m vminus eta : ℝ) : ℝ :=
  eta * rho alpha m ^ 2 / (3 * Real.pi * vminus * m)

noncomputable def costThreeHalves (alpha m vminus : ℝ) : ℝ :=
  rho alpha m ^ (5 / 2 : ℝ) /
    (16 * Real.sqrt (2 * Real.pi) * (vminus * m) ^ (3 / 2 : ℝ))

noncomputable def tailCost (alpha m vminus T : ℝ) : ℝ :=
  (1 - T / Real.pi) * Real.exp (-vminus * (alpha * m) * T ^ 2 / 2) +
    Real.exp (-vminus * (alpha * m) * T ^ 2 / 2) /
      (Real.pi * vminus * (alpha * m) * T)

noncomputable def envelope (alpha m vminus eta T y : ℝ) : ℝ :=
  costOne alpha m vminus eta * y ^ (-1 : ℝ) +
    costThreeHalves alpha m vminus * y ^ (-(3 / 2 : ℝ)) +
    tailCost alpha m vminus T

theorem rho_pos {alpha m : ℝ} (ham : 1 < alpha * m) : 0 < rho alpha m := by
  unfold rho
  exact div_pos (by linarith) (by linarith)

theorem rho_antitone {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) :
    y / (y - 1) ≤ x / (x - 1) := by
  apply (div_le_div_iff₀ (by linarith : 0 < y - 1) (by linarith : 0 < x - 1)).mpr
  nlinarith

theorem costOne_nonneg {alpha m vminus eta : ℝ}
    (hm : 0 ≤ m) (hv : 0 ≤ vminus) (heta : 0 ≤ eta) :
    0 ≤ costOne alpha m vminus eta := by
  unfold costOne
  positivity

theorem costThreeHalves_nonneg {alpha m vminus : ℝ}
    (hm : 0 < m) (ham : 1 < alpha * m) (hv : 0 < vminus) :
    0 ≤ costThreeHalves alpha m vminus := by
  have hr := rho_pos ham
  unfold costThreeHalves
  positivity

theorem tailCost_nonneg {alpha m vminus q T : ℝ}
    (ham : 1 < alpha * m) (hv : 0 < vminus) (hcut : BernoulliCutoff.Valid q T) :
    0 ≤ tailCost alpha m vminus T := by
  have ha : 0 < alpha * m := by linarith
  have ht := hcut.positive
  have hfactor : 0 ≤ 1 - T / Real.pi := by
    have := (div_lt_one Real.pi_pos).mpr hcut.period
    linarith
  unfold tailCost
  positivity

theorem scaled_power_cost {M m v : ℝ} (hM : 0 < M) (hm : 0 < m) (hv : 0 < v)
    (C p : ℝ) :
    C / (v * m) ^ p * (M / m) ^ (-p) = C / (M * v) ^ p := by
  rw [Real.rpow_neg (div_nonneg hM.le hm.le), Real.div_rpow hM.le hm.le,
    Real.mul_rpow hv.le hm.le, Real.mul_rpow hM.le hv.le]
  have hnM : M ^ p ≠ 0 := (Real.rpow_pos_of_pos hM p).ne'
  have hnm : m ^ p ≠ 0 := (Real.rpow_pos_of_pos hm p).ne'
  have hnv : v ^ p ≠ 0 := (Real.rpow_pos_of_pos hv p).ne'
  field_simp

theorem first_cost_scaled {M m v alpha eta : ℝ}
    (hM : 0 < M) (hm : 0 < m) (hv : 0 < v) :
    costOne alpha m v eta * (M / m) ^ (-1 : ℝ) =
      eta * rho alpha m ^ 2 / (3 * Real.pi * (M * v)) := by
  rw [Real.rpow_neg_one]
  unfold costOne
  field_simp

theorem second_cost_scaled {M m v alpha : ℝ}
    (hM : 0 < M) (hm : 0 < m) (hv : 0 < v) :
    costThreeHalves alpha m v * (M / m) ^ (-(3 / 2 : ℝ)) =
      rho alpha m ^ (5 / 2 : ℝ) /
        (16 * Real.sqrt (2 * Real.pi) * (M * v) ^ (3 / 2 : ℝ)) := by
  unfold costThreeHalves
  rw [← div_div]
  rw [scaled_power_cost hM hm hv]
  rw [div_div]

theorem first_cost_bound {M m v vminus alpha eta : ℝ}
    (hm : 0 < m) (ham : 1 < alpha * m) (hM : alpha * m ≤ M)
    (hvm : 0 < vminus) (hv : vminus ≤ v) {asym : ℝ}
    (ha : 0 ≤ asym) (heta : asym ≤ eta) :
    asym * (M / (M - 1)) ^ 2 / (3 * Real.pi * (M * v)) ≤
      costOne alpha m vminus eta * (M / m) ^ (-1 : ℝ) := by
  have hM0 : 0 < M := by linarith
  have hv0 : 0 < v := hvm.trans_le hv
  have hMsub : 0 < M - 1 := by linarith
  have heta0 : 0 ≤ eta := ha.trans heta
  have hrho := rho_pos ham
  have hr : 0 ≤ M / (M - 1) := by positivity
  have hrle : M / (M - 1) ≤ rho alpha m := rho_antitone ham hM
  have hden : 3 * Real.pi * (M * vminus) ≤ 3 * Real.pi * (M * v) := by gcongr
  rw [first_cost_scaled hM0 hm hvm]
  exact div_le_div₀ (by positivity) (mul_le_mul heta (pow_le_pow_left₀ hr hrle 2) (sq_nonneg _) (by linarith))
    (by positivity) hden

theorem second_cost_bound {M m v vminus alpha : ℝ}
    (hm : 0 < m) (ham : 1 < alpha * m) (hM : alpha * m ≤ M)
    (hvm : 0 < vminus) (hv : vminus ≤ v) :
    (M / (M - 1)) ^ (5 / 2 : ℝ) /
        (16 * Real.sqrt (2 * Real.pi) * (M * v) ^ (3 / 2 : ℝ)) ≤
      costThreeHalves alpha m vminus * (M / m) ^ (-(3 / 2 : ℝ)) := by
  have hM0 : 0 < M := by linarith
  have hv0 : 0 < v := hvm.trans_le hv
  have hMsub : 0 < M - 1 := by linarith
  have hrho := rho_pos ham
  have hr : 0 ≤ M / (M - 1) := by positivity
  have hrle : M / (M - 1) ≤ rho alpha m := rho_antitone ham hM
  rw [second_cost_scaled hM0 hm hvm]
  have hnum := Real.rpow_le_rpow hr hrle (by norm_num : (0:ℝ) ≤ 5/2)
  have hden : 16 * Real.sqrt (2 * Real.pi) * (M * vminus) ^ (3 / 2 : ℝ) ≤
      16 * Real.sqrt (2 * Real.pi) * (M * v) ^ (3 / 2 : ℝ) := by
    gcongr
  exact div_le_div₀ (by positivity) hnum (by positivity) hden

theorem tail_cost_bound {M m v vminus alpha q T : ℝ}
    (ham : 1 < alpha * m) (hM : alpha * m ≤ M)
    (hvm : 0 < vminus) (hv : vminus ≤ v) (hcut : BernoulliCutoff.Valid q T) :
    (1 - T / Real.pi) * Real.exp (-(M * v) * T ^ 2 / 2) +
      Real.exp (-(M * v) * T ^ 2 / 2) / (Real.pi * (M * v) * T) ≤
        tailCost alpha m vminus T := by
  have ha : 0 < alpha * m := by linarith
  have hM0 : 0 < M := by linarith
  have ht := hcut.positive
  have hv0 : 0 < v := hvm.trans_le hv
  have hav : vminus * (alpha * m) ≤ M * v := by
    calc
      _ = (alpha * m) * vminus := mul_comm _ _
      _ ≤ M * v := mul_le_mul hM hv hvm.le hM0.le
  have he : Real.exp (-(M * v) * T ^ 2 / 2) ≤
      Real.exp (-vminus * (alpha * m) * T ^ 2 / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hav (sq_nonneg T)]
  have hfactor : 0 ≤ 1 - T / Real.pi := by
    have := (div_lt_one Real.pi_pos).mpr hcut.period
    linarith
  unfold tailCost
  apply add_le_add (mul_le_mul_of_nonneg_left he hfactor)
  apply div_le_div₀ (by positivity) he (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hav (show 0 ≤ Real.pi * T by positivity)]

/-- The actual point mass, uniformly priced over all admissible free counts. -/
theorem error_le_envelope (M : ℕ) (j : ℤ) {alpha m vminus eta q T : ℝ}
    (hm : 0 < m) (hcut : BernoulliCutoff.Valid q T)
    (ham : 1 < alpha * m) (hM : alpha * m ≤ (M : ℝ))
    (hvm : 0 < vminus) (hv : vminus ≤ q * (1 - q)) (heta : |1 - 2 * q| ≤ eta) :
    |binomialMass M j q - BinomialPointMassError.gaussianDensity
      ((M : ℝ) * (q * (1 - q))) ((j : ℝ) - M * q)| ≤
      envelope alpha m vminus eta T ((M : ℝ) / m) := by
  have hM1 : 1 < M := by exact_mod_cast (ham.trans_le hM)
  have he := BinomialPointMassError.binomial_pointMass_error_bound M (by omega) j hcut
  dsimp only at he
  apply he.trans
  unfold envelope
  have h1 := first_cost_bound hm ham hM hvm hv (abs_nonneg (1-2*q)) heta
  have h2 := second_cost_bound hm ham hM hvm hv
  have ht := tail_cost_bound ham hM hvm hv hcut
  linarith

#print axioms scaled_power_cost
#print axioms error_le_envelope
end ForestUnimodality.PointMassErrorEnvelope
