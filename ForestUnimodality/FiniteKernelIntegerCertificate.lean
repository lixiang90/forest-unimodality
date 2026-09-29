import ForestUnimodality.FiniteKernelIntegerResidual
import ForestUnimodality.BinomialMassIntegerCertificate

/-! Complete checked finite-degree certificates with shared-denominator
mass enclosures and integer residual loops. The original binomial law,
curvature price, and full real parameter interval are all retained. -/
namespace ForestUnimodality.BinomialMassIntervalCertificate

open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate

def IntegerTable.lowerNumeratorInt {n : ℕ} (t : IntegerTable n) (j : ℤ) : ℤ :=
  if 0 ≤ j ∧ j ≤ n then t.lowerNumerator j.toNat else 0

def IntegerTable.upperNumeratorInt {n : ℕ} (t : IntegerTable n) (j : ℤ) : ℤ :=
  if 0 ≤ j ∧ j ≤ n then t.upperNumerator j.toNat else 0

theorem IntegerTable.integer_sound {n : ℕ} (t : IntegerTable n) (a b : ℕ)
    (h : t.check a b = true) (j : ℤ) :
    (t.lowerNumeratorInt j : ℚ) / t.denominator ≤ mass n j ((a : ℚ) / b) ∧
    mass n j ((a : ℚ) / b) ≤ (t.upperNumeratorInt j : ℚ) / t.denominator := by
  by_cases hj : 0 ≤ j ∧ j ≤ n
  · have hn : j.toNat ≤ n := by omega
    have he : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj.1
    have hb := t.check_sound h j.toNat hn
    simpa only [lowerNumeratorInt, upperNumeratorInt, if_pos hj, he, lower, upper] using hb
  · simp [lowerNumeratorInt, upperNumeratorInt, mass, hj]

structure IntegerEndpointWitness (n : ℕ) where
  qNumerator : ℕ
  qDenominator : ℕ
  table : IntegerTable n
  base : ℚ
  polynomial : IntegerResidualPolynomial

def IntegerEndpointWitness.q {n : ℕ} (e : IntegerEndpointWitness n) : ℚ :=
  (e.qNumerator : ℚ) / e.qDenominator

def IntegerEndpointWitness.check {ι : Type*} {n : ℕ} (e : IntegerEndpointWitness n)
    (r : RationalRow ι) (a b bd bc : ℚ) : Bool :=
  e.table.check e.qNumerator e.qDenominator &&
    e.polynomial.check r n e.q e.base e.table.denominator &&
    decide (e.base ≤ r.tailBase n a b bd bc e.q) &&
    e.polynomial.spanCheck n e.table.lowerNumeratorInt e.table.upperNumeratorInt &&
    QuadraticCertificate.leftRayCheck r.dδ (-r.C) e.base (-2 - e.q * n) &&
    QuadraticCertificate.rayCheck r.dδ (-r.C) e.base ((n : ℚ) + 2 - e.q * n)

theorem IntegerEndpointWitness.check_sound {ι : Type*} {n : ℕ} (e : IntegerEndpointWitness n)
    (r : RationalRow ι) (a b bd bc : ℚ) (hf : r.fixedIndices = ∅)
    (hscale : 0 ≤ r.scale) (hwL : 0 ≤ r.wL) (hwR : 0 ≤ r.wR) (hwC : 0 ≤ r.wC)
    (hc : e.check r a b bd bc = true) (j : ℤ) :
    (b - a) ^ 2 * r.curvaturePrice n j a bd bc / 8 ≤ r.residual n j e.q := by
  have hp : e.table.check e.qNumerator e.qDenominator = true ∧
      e.polynomial.check r n e.q e.base e.table.denominator = true ∧
      e.base ≤ r.tailBase n a b bd bc e.q ∧
      e.polynomial.spanCheck n e.table.lowerNumeratorInt e.table.upperNumeratorInt = true ∧
      QuadraticCertificate.leftRayCheck r.dδ (-r.C) e.base (-2 - e.q * n) = true ∧
      QuadraticCertificate.rayCheck r.dδ (-r.C) e.base ((n : ℚ) + 2 - e.q * n) = true := by
    simpa only [check, Bool.and_eq_true_iff, decide_eq_true_eq, and_assoc] using hc
  have hv : e.table.toTable.Valid e.q := IntegerTable.toTable_valid (of_decide_eq_true hp.1)
  have hs := e.polynomial.spanCheck_sound r n e.q e.base e.table.denominator hp.2.1
    e.table.lowerNumeratorInt e.table.upperNumeratorInt hp.2.2.2.1
  have he : r.roundedEndpointCheck n a b bd bc e.q e.base
      (fun s => (e.table.lowerNumeratorInt s : ℚ) / e.table.denominator)
      (fun s => (e.table.upperNumeratorInt s : ℚ) / e.table.denominator) = true := by
    simp only [RationalRow.roundedEndpointCheck, Bool.and_eq_true_iff, decide_eq_true_eq, and_assoc]
    exact ⟨hp.2.2.1, hs, hp.2.2.2.2.1, hp.2.2.2.2.2⟩
  exact r.roundedEndpointCheck_sound hf n a b bd bc e.q e.base _ _
    hscale hwL hwR hwC hv.1.le hv.2.1.le he
    (fun j => (e.table.integer_sound e.qNumerator e.qDenominator hp.1 j).1)
    (fun j => (e.table.integer_sound e.qNumerator e.qDenominator hp.1 j).2) j

structure IntegerDegreeWitness (n : ℕ) where
  curvature : DegreeWitness
  endpointA : IntegerEndpointWitness n
  endpointB : IntegerEndpointWitness n

def IntegerDegreeWitness.check {ι : Type*} {n : ℕ} (d : IntegerDegreeWitness n)
    (r : RationalRow ι) (w : IntervalWitness) : Bool :=
  decide (r.fixedIndices = ∅ ∧ d.endpointA.q = w.lo ∧ d.endpointB.q = w.hi) &&
    d.curvature.check n w.damping &&
    d.endpointA.check r w.lo w.hi (d.curvature.directionUpper n w.damping)
      (d.curvature.centralUpper n w.damping) &&
    d.endpointB.check r w.lo w.hi (d.curvature.directionUpper n w.damping)
      (d.curvature.centralUpper n w.damping)

theorem IntegerDegreeWitness.check_sound {ι : Type*} [DecidableEq ι] {n : ℕ}
    (d : IntegerDegreeWitness n) (r : RationalRow ι) (w : IntervalWitness)
    (hr : r.signCheck = true) (hw : w.check = true) (hd : d.check r w = true)
    (j : ℤ) {q : ℝ} (hq : q ∈ Set.Icc (w.lo : ℝ) (w.hi : ℝ)) :
    0 ≤ r.toReal.residual n j q := by
  have hp : (r.fixedIndices = ∅ ∧ d.endpointA.q = w.lo ∧ d.endpointB.q = w.hi) ∧
      d.curvature.check n w.damping = true ∧
      d.endpointA.check r w.lo w.hi (d.curvature.directionUpper n w.damping)
        (d.curvature.centralUpper n w.damping) = true ∧
      d.endpointB.check r w.lo w.hi (d.curvature.directionUpper n w.damping)
        (d.curvature.centralUpper n w.damping) = true := by
    simpa only [check, Bool.and_eq_true_iff, decide_eq_true_eq, and_assoc] using hd
  have hsign := of_decide_eq_true hr
  have hs : 0 < r.scale ∧ 0 ≤ r.wL ∧ 0 ≤ r.wR ∧ 0 ≤ r.wC :=
    ⟨hsign.1.1, hsign.1.2.1, hsign.1.2.2.1, hsign.1.2.2.2.1⟩
  have hA := d.endpointA.check_sound r w.lo w.hi _ _ hp.1.1
    hs.1.le hs.2.1 hs.2.2.1 hs.2.2.2 hp.2.2.1 j
  have hB := d.endpointB.check_sound r w.lo w.hi _ _ hp.1.1
    hs.1.le hs.2.1 hs.2.2.1 hs.2.2.2 hp.2.2.2 j
  rw [hp.1.2.1] at hA
  rw [hp.1.2.2] at hB
  have he : r.endpointCheck n j w.lo w.hi (d.curvature.directionUpper n w.damping)
      (d.curvature.centralUpper n w.damping) = true := decide_eq_true ⟨hA, hB⟩
  exact r.checked_state_sound w d.curvature n j hr hw hp.2.1 he hq

#print axioms IntegerTable.integer_sound
#print axioms IntegerEndpointWitness.check_sound
#print axioms IntegerDegreeWitness.check_sound

end ForestUnimodality.BinomialMassIntervalCertificate
