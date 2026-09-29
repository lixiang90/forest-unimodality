import ForestUnimodality.FiniteKernelRationalCertificate
import ForestUnimodality.QuadraticCertificate

/-! The old stage170/130/99 certificates cover every integer offset.
Outside the finite binomial support the complete residual is a quadratic;
the half-line tests include its possible interior vertex. -/
namespace ForestUnimodality.FiniteKernelRationalCertificate

open Finset FiniteKernelCurvatureCertificate

theorem kernel_zero_left (n : ℕ) (j : ℤ) (q wL wR wC : ℚ) (hj : j ≤ -2) :
    kernel n j q wL wR wC = 0 := by
  simp [kernel, mass, show ¬0 ≤ j by omega, show ¬1 ≤ j by omega,
    show ¬0 ≤ j + 1 by omega]

theorem kernel_zero_right (n : ℕ) (j : ℤ) (q wL wR wC : ℚ) (hj : (n : ℤ) + 2 ≤ j) :
    kernel n j q wL wR wC = 0 := by
  simp [kernel, mass, show ¬j ≤ (n : ℤ) by omega, show ¬j - 1 ≤ (n : ℤ) by omega,
    show ¬j + 1 ≤ (n : ℤ) by omega]

def RationalRow.tailBase {ι : Type*} (r : RationalRow ι)
    (n : ℕ) (a b bd bc q : ℚ) : ℚ :=
  -r.A - r.B * n + r.dM * (n : ℚ) ^ 2 +
    (∑ i ∈ r.terms, r.price i * (1 - q + q * r.retention i) ^ n) -
    (b - a) ^ 2 * r.curvaturePrice n 0 a bd bc / 8

def RationalRow.tailCheck {ι : Type*} (r : RationalRow ι)
    (n : ℕ) (a b bd bc q : ℚ) : Bool :=
  decide (r.fixedIndices = ∅) &&
  QuadraticCertificate.leftRayCheck r.dδ (-r.C) (r.tailBase n a b bd bc q) (-2 - q * n) &&
  QuadraticCertificate.rayCheck r.dδ (-r.C) (r.tailBase n a b bd bc q) ((n : ℚ) + 2 - q * n)

theorem RationalRow.curvaturePrice_eq_zero_index {ι : Type*} (r : RationalRow ι)
    (hf : r.fixedIndices = ∅) (n : ℕ) (j : ℤ) (a bd bc : ℚ) :
    r.curvaturePrice n j a bd bc = r.curvaturePrice n 0 a bd bc := by
  simp [curvaturePrice, fixed, hf]

theorem RationalRow.residual_sub_price_eq_quadratic {ι : Type*} (r : RationalRow ι)
    (hf : r.fixedIndices = ∅) (n : ℕ) (j : ℤ) (a b bd bc q : ℚ)
    (hk : kernel n j q r.wL r.wR r.wC = 0) :
    r.residual n j q - (b - a) ^ 2 * r.curvaturePrice n j a bd bc / 8 =
      r.dδ * ((j : ℚ) - q * n) ^ 2 - r.C * ((j : ℚ) - q * n) + r.tailBase n a b bd bc q := by
  rw [r.curvaturePrice_eq_zero_index hf]
  simp only [residual, hk, mul_zero, fixed, hf, Finset.notMem_empty, if_false, zero_mul]
  unfold tailBase
  ring

theorem RationalRow.tailCheck_sound {ι : Type*} (r : RationalRow ι)
    (n : ℕ) (a b bd bc q : ℚ) (hc : r.tailCheck n a b bd bc q = true)
    (j : ℤ) (hj : j ≤ -2 ∨ (n : ℤ) + 2 ≤ j) :
    (b - a) ^ 2 * r.curvaturePrice n j a bd bc / 8 ≤ r.residual n j q := by
  have hp : r.fixedIndices = ∅ ∧
      QuadraticCertificate.leftRayCheck r.dδ (-r.C) (r.tailBase n a b bd bc q) (-2 - q * n) = true ∧
      QuadraticCertificate.rayCheck r.dδ (-r.C) (r.tailBase n a b bd bc q) ((n : ℚ) + 2 - q * n) = true := by
    simpa only [tailCheck, Bool.and_eq_true_iff, decide_eq_true_eq, and_assoc] using hc
  have hquad : 0 ≤ r.dδ * ((j : ℚ) - q * n) ^ 2 - r.C * ((j : ℚ) - q * n) +
      r.tailBase n a b bd bc q := by
    have hreal : (0 : ℝ) ≤ (r.dδ : ℝ) * (((j : ℚ) - q * n : ℚ) : ℝ) ^ 2 +
        ((-r.C : ℚ) : ℝ) * (((j : ℚ) - q * n : ℚ) : ℝ) + r.tailBase n a b bd bc q := by
      rcases hj with hj | hj
      · have hbound : ((j : ℚ) - q * n : ℚ) ≤ -2 - q * n := by
          have hj' : (j : ℚ) ≤ -2 := by exact_mod_cast hj
          linarith
        have h := QuadraticCertificate.leftRayCheck_sound hp.2.1
          (show (((j : ℚ) - q * n : ℚ) : ℝ) ≤ ((-2 - q * n : ℚ) : ℝ) by exact_mod_cast hbound)
        simpa only [QuadraticCertificate.evalReal_quadratic] using h
      · have hbound : (n : ℚ) + 2 - q * n ≤ (j : ℚ) - q * n := by
          have hj' : (n : ℚ) + 2 ≤ (j : ℚ) := by exact_mod_cast hj
          linarith
        have h := QuadraticCertificate.rayCheck_sound hp.2.2
          (show (((n : ℚ) + 2 - q * n : ℚ) : ℝ) ≤ (((j : ℚ) - q * n : ℚ) : ℝ) by exact_mod_cast hbound)
        simpa only [QuadraticCertificate.evalReal_quadratic] using h
    have hQ : (0 : ℚ) ≤ r.dδ * ((j : ℚ) - q * n) ^ 2 +
        (-r.C) * ((j : ℚ) - q * n) + r.tailBase n a b bd bc q := by exact_mod_cast hreal
    nlinarith
  apply sub_nonneg.mp
  rw [r.residual_sub_price_eq_quadratic hp.1 n j a b bd bc q]
  · exact hquad
  · rcases hj with hj | hj
    · exact kernel_zero_left n j q _ _ _ hj
    · exact kernel_zero_right n j q _ _ _ hj

def RationalRow.allIntegerCheck {ι : Type*} (r : RationalRow ι) (w : IntervalWitness)
    (d : DegreeWitness) (n : ℕ) : Bool :=
  r.spanCheck w d n &&
    r.tailCheck n w.lo w.hi (d.directionUpper n w.damping) (d.centralUpper n w.damping) w.lo &&
    r.tailCheck n w.lo w.hi (d.directionUpper n w.damping) (d.centralUpper n w.damping) w.hi

theorem RationalRow.allIntegerCheck_sound {ι : Type*} [DecidableEq ι]
    (r : RationalRow ι) (w : IntervalWitness) (d : DegreeWitness) (n : ℕ)
    (hr : r.signCheck = true) (hw : w.check = true) (hs : r.allIntegerCheck w d n = true)
    (j : ℤ) {q : ℝ} (hq : q ∈ Set.Icc (w.lo : ℝ) (w.hi : ℝ)) :
    0 ≤ r.toReal.residual n j q := by
  have hp : r.spanCheck w d n = true ∧
      r.tailCheck n w.lo w.hi (d.directionUpper n w.damping) (d.centralUpper n w.damping) w.lo = true ∧
      r.tailCheck n w.lo w.hi (d.directionUpper n w.damping) (d.centralUpper n w.damping) w.hi = true := by
    simpa only [allIntegerCheck, Bool.and_eq_true_iff, and_assoc] using hs
  by_cases hspan : -2 ≤ j ∧ j ≤ (n : ℤ) + 2
  · exact r.spanCheck_sound w d n hr hw hp.1 hspan.1 hspan.2 hq
  · have hj : j ≤ -2 ∨ (n : ℤ) + 2 ≤ j := by omega
    have hd := (Bool.and_eq_true_iff.mp hp.1).1
    have he : r.endpointCheck n j w.lo w.hi (d.directionUpper n w.damping)
        (d.centralUpper n w.damping) = true := by
      apply decide_eq_true
      exact ⟨r.tailCheck_sound n _ _ _ _ _ hp.2.1 j hj,
        r.tailCheck_sound n _ _ _ _ _ hp.2.2 j hj⟩
    exact r.checked_state_sound w d n j hr hw hd he hq

#print axioms RationalRow.tailCheck_sound
#print axioms RationalRow.allIntegerCheck_sound

end ForestUnimodality.FiniteKernelRationalCertificate
