import ForestUnimodality.FiniteKernelInfiniteTails

/-! Fixed precision probability intervals may be reused by many certificate
rows. The long Laplace and curvature arithmetic is checked once at each
endpoint; each integer state then needs only a short rational quadratic.
All estimates remain one-sided inequalities about the original residual. -/
namespace ForestUnimodality.FiniteKernelRationalCertificate

open Finset FiniteKernelCurvatureCertificate

def kernelLower (j : ℤ) (q wL wR wC : ℚ) (lo hi : ℤ → ℚ) : ℚ :=
  wL * ((1 - q) * lo j - q * hi (j - 1)) +
  wR * (q * lo j - (1 - q) * hi (j + 1)) +
  wC * (2 * lo j - hi (j - 1) - hi (j + 1))

theorem kernelLower_le (n : ℕ) (j : ℤ) (q wL wR wC : ℚ) (lo hi : ℤ → ℚ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hwL : 0 ≤ wL) (hwR : 0 ≤ wR) (hwC : 0 ≤ wC)
    (hlo : ∀ s, lo s ≤ mass n s q) (hhi : ∀ s, mass n s q ≤ hi s) :
    kernelLower j q wL wR wC lo hi ≤ kernel n j q wL wR wC := by
  have hqc : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  have hL := sub_le_sub (mul_le_mul_of_nonneg_left (hlo j) hqc)
    (mul_le_mul_of_nonneg_left (hhi (j - 1)) hq0)
  have hR := sub_le_sub (mul_le_mul_of_nonneg_left (hlo j) hq0)
    (mul_le_mul_of_nonneg_left (hhi (j + 1)) hqc)
  have hC := sub_le_sub (sub_le_sub (mul_le_mul_of_nonneg_left (hlo j) (by norm_num : (0:ℚ) ≤ 2))
    (hhi (j - 1))) (hhi (j + 1))
  exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hL hwL)
    (mul_le_mul_of_nonneg_left hR hwR)) (mul_le_mul_of_nonneg_left hC hwC)

def RationalRow.shortResidual {ι : Type*} (r : RationalRow ι)
    (n : ℕ) (j : ℤ) (q base : ℚ) (lo hi : ℤ → ℚ) : ℚ :=
  r.scale * kernelLower j q r.wL r.wR r.wC lo hi +
    r.dδ * ((j : ℚ) - q * n) ^ 2 - r.C * ((j : ℚ) - q * n) + base

theorem RationalRow.residual_sub_price_eq {ι : Type*} (r : RationalRow ι)
    (hf : r.fixedIndices = ∅) (n : ℕ) (j : ℤ) (a b bd bc q : ℚ) :
    r.residual n j q - (b - a) ^ 2 * r.curvaturePrice n j a bd bc / 8 =
      r.scale * kernel n j q r.wL r.wR r.wC +
      r.dδ * ((j : ℚ) - q * n) ^ 2 - r.C * ((j : ℚ) - q * n) + r.tailBase n a b bd bc q := by
  rw [r.curvaturePrice_eq_zero_index hf]
  simp only [residual, fixed, hf, Finset.notMem_empty, if_false, zero_mul]
  unfold tailBase
  ring

theorem RationalRow.shortResidual_le {ι : Type*} (r : RationalRow ι)
    (hf : r.fixedIndices = ∅) (n : ℕ) (j : ℤ) (a b bd bc q base : ℚ) (lo hi : ℤ → ℚ)
    (hscale : 0 ≤ r.scale) (hwL : 0 ≤ r.wL) (hwR : 0 ≤ r.wR) (hwC : 0 ≤ r.wC)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hbase : base ≤ r.tailBase n a b bd bc q)
    (hlo : ∀ s, lo s ≤ mass n s q) (hhi : ∀ s, mass n s q ≤ hi s) :
    r.shortResidual n j q base lo hi ≤
      r.residual n j q - (b - a) ^ 2 * r.curvaturePrice n j a bd bc / 8 := by
  rw [r.residual_sub_price_eq hf]
  have hk := mul_le_mul_of_nonneg_left (kernelLower_le n j q _ _ _ lo hi
    hq0 hq1 hwL hwR hwC hlo hhi) hscale
  unfold shortResidual
  linarith

def RationalRow.roundedEndpointCheck {ι : Type*} (r : RationalRow ι)
    (n : ℕ) (a b bd bc q base : ℚ) (lo hi : ℤ → ℚ) : Bool :=
  decide (base ≤ r.tailBase n a b bd bc q) &&
    (List.range (n + 5)).all (fun i => decide (0 ≤ r.shortResidual n ((i : ℤ) - 2) q base lo hi)) &&
    QuadraticCertificate.leftRayCheck r.dδ (-r.C) base (-2 - q * n) &&
    QuadraticCertificate.rayCheck r.dδ (-r.C) base ((n : ℚ) + 2 - q * n)

theorem RationalRow.roundedEndpointCheck_sound {ι : Type*} (r : RationalRow ι)
    (hf : r.fixedIndices = ∅) (n : ℕ) (a b bd bc q base : ℚ) (lo hi : ℤ → ℚ)
    (hscale : 0 ≤ r.scale) (hwL : 0 ≤ r.wL) (hwR : 0 ≤ r.wR) (hwC : 0 ≤ r.wC)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hc : r.roundedEndpointCheck n a b bd bc q base lo hi = true)
    (hlo : ∀ s, lo s ≤ mass n s q) (hhi : ∀ s, mass n s q ≤ hi s) (j : ℤ) :
    (b - a) ^ 2 * r.curvaturePrice n j a bd bc / 8 ≤ r.residual n j q := by
  have hp : base ≤ r.tailBase n a b bd bc q ∧
      (∀ i ∈ List.range (n + 5), 0 ≤ r.shortResidual n ((i : ℤ) - 2) q base lo hi) ∧
      QuadraticCertificate.leftRayCheck r.dδ (-r.C) base (-2 - q * n) = true ∧
      QuadraticCertificate.rayCheck r.dδ (-r.C) base ((n : ℚ) + 2 - q * n) = true := by
    simpa only [roundedEndpointCheck, Bool.and_eq_true_iff, decide_eq_true_eq,
      List.all_eq_true, and_assoc] using hc
  apply sub_nonneg.mp
  by_cases hspan : -2 ≤ j ∧ j ≤ (n : ℤ) + 2
  · have hm : (j + 2).toNat ∈ List.range (n + 5) := by simp only [List.mem_range]; omega
    have he := hp.2.1 (j + 2).toNat hm
    rw [show ((j + 2).toNat : ℤ) - 2 = j by omega] at he
    exact he.trans (r.shortResidual_le hf n j a b bd bc q base lo hi
      hscale hwL hwR hwC hq0 hq1 hp.1 hlo hhi)
  · have hj : j ≤ -2 ∨ (n : ℤ) + 2 ≤ j := by omega
    have hk : kernel n j q r.wL r.wR r.wC = 0 := by
      rcases hj with hj | hj
      · exact kernel_zero_left n j q _ _ _ hj
      · exact kernel_zero_right n j q _ _ _ hj
    rw [r.residual_sub_price_eq_quadratic hf n j a b bd bc q hk]
    have hquad : 0 ≤ r.dδ * ((j : ℚ) - q * n) ^ 2 - r.C * ((j : ℚ) - q * n) + base := by
      have hR : (0 : ℝ) ≤ (r.dδ : ℝ) * (((j : ℚ) - q * n : ℚ) : ℝ) ^ 2 +
          ((-r.C : ℚ) : ℝ) * (((j : ℚ) - q * n : ℚ) : ℝ) + base := by
        rcases hj with hj | hj
        · have hb : ((j : ℚ) - q * n : ℚ) ≤ -2 - q * n := by
            have hj' : (j : ℚ) ≤ -2 := by exact_mod_cast hj
            linarith
          simpa only [QuadraticCertificate.evalReal_quadratic] using
            QuadraticCertificate.leftRayCheck_sound hp.2.2.1
              (show (((j : ℚ) - q * n : ℚ) : ℝ) ≤ ((-2 - q * n : ℚ) : ℝ) by exact_mod_cast hb)
        · have hb : (n : ℚ) + 2 - q * n ≤ (j : ℚ) - q * n := by
            have hj' : (n : ℚ) + 2 ≤ (j : ℚ) := by exact_mod_cast hj
            linarith
          simpa only [QuadraticCertificate.evalReal_quadratic] using
            QuadraticCertificate.rayCheck_sound hp.2.2.2
              (show (((n : ℚ) + 2 - q * n : ℚ) : ℝ) ≤ (((j : ℚ) - q * n : ℚ) : ℝ) by exact_mod_cast hb)
      have hQ : (0 : ℚ) ≤ r.dδ * ((j : ℚ) - q * n) ^ 2 + (-r.C) * ((j : ℚ) - q * n) + base := by
        exact_mod_cast hR
      nlinarith
    linarith

def RationalRow.roundedDegreeCheck {ι : Type*} (r : RationalRow ι)
    (w : IntervalWitness) (d : DegreeWitness) (n : ℕ) (baseA baseB : ℚ)
    (loA hiA loB hiB : ℤ → ℚ) : Bool :=
  decide (r.fixedIndices = ∅) && d.check n w.damping &&
    r.roundedEndpointCheck n w.lo w.hi (d.directionUpper n w.damping)
      (d.centralUpper n w.damping) w.lo baseA loA hiA &&
    r.roundedEndpointCheck n w.lo w.hi (d.directionUpper n w.damping)
      (d.centralUpper n w.damping) w.hi baseB loB hiB

theorem RationalRow.roundedDegreeCheck_sound {ι : Type*} [DecidableEq ι]
    (r : RationalRow ι) (w : IntervalWitness) (d : DegreeWitness) (n : ℕ)
    (baseA baseB : ℚ) (loA hiA loB hiB : ℤ → ℚ)
    (hr : r.signCheck = true) (hw : w.check = true)
    (hc : r.roundedDegreeCheck w d n baseA baseB loA hiA loB hiB = true)
    (hloA : ∀ j, loA j ≤ mass n j w.lo) (hhiA : ∀ j, mass n j w.lo ≤ hiA j)
    (hloB : ∀ j, loB j ≤ mass n j w.hi) (hhiB : ∀ j, mass n j w.hi ≤ hiB j)
    (j : ℤ) {q : ℝ} (hq : q ∈ Set.Icc (w.lo : ℝ) (w.hi : ℝ)) :
    0 ≤ r.toReal.residual n j q := by
  have hp : r.fixedIndices = ∅ ∧ d.check n w.damping = true ∧
      r.roundedEndpointCheck n w.lo w.hi (d.directionUpper n w.damping)
        (d.centralUpper n w.damping) w.lo baseA loA hiA = true ∧
      r.roundedEndpointCheck n w.lo w.hi (d.directionUpper n w.damping)
        (d.centralUpper n w.damping) w.hi baseB loB hiB = true := by
    simpa only [roundedDegreeCheck, Bool.and_eq_true_iff, decide_eq_true_eq, and_assoc] using hc
  have hsign := of_decide_eq_true hr
  have hsign' : 0 < r.scale ∧ 0 ≤ r.wL ∧ 0 ≤ r.wR ∧ 0 ≤ r.wC :=
    ⟨hsign.1.1, hsign.1.2.1, hsign.1.2.2.1, hsign.1.2.2.2.1⟩
  have hi := of_decide_eq_true hw
  have he : r.endpointCheck n j w.lo w.hi (d.directionUpper n w.damping)
      (d.centralUpper n w.damping) = true := by
    apply decide_eq_true
    constructor
    · exact r.roundedEndpointCheck_sound hp.1 n _ _ _ _ w.lo baseA loA hiA
        hsign'.1.le hsign'.2.1 hsign'.2.2.1 hsign'.2.2.2 hi.1
        (hi.2.1.trans hi.2.2.1) hp.2.2.1 hloA hhiA j
    · exact r.roundedEndpointCheck_sound hp.1 n _ _ _ _ w.hi baseB loB hiB
        hsign'.1.le hsign'.2.1 hsign'.2.2.1 hsign'.2.2.2
        (hi.1.trans hi.2.1) hi.2.2.1 hp.2.2.2 hloB hhiB j
  exact r.checked_state_sound w d n j hr hw hp.2.1 he hq

#print axioms kernelLower_le
#print axioms RationalRow.roundedEndpointCheck_sound
#print axioms RationalRow.roundedDegreeCheck_sound

end ForestUnimodality.FiniteKernelRationalCertificate
