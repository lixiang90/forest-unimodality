import ForestUnimodality.FiniteKernelRationalCertificate

/-! A full-real-parameter certificate on an explicitly supported finite
set of integer shifts, including arbitrary nonnegative fixed-shift fees. -/
namespace ForestUnimodality.FiniteKernelRationalCertificate
open FiniteKernelCurvatureCertificate

def RationalRow.supportedDegreeCheck {ι : Type*} (r : RationalRow ι)
    (w : IntervalWitness) (d : DegreeWitness) (n : ℕ) (shifts : List ℤ) : Bool :=
  d.check n w.damping && shifts.all fun j =>
    r.endpointCheck n j w.lo w.hi (d.directionUpper n w.damping) (d.centralUpper n w.damping)

theorem RationalRow.supportedDegreeCheck_sound {ι : Type*} [DecidableEq ι]
    (r : RationalRow ι) (w : IntervalWitness) (d : DegreeWitness) (n : ℕ) (shifts : List ℤ)
    (hr : r.signCheck = true) (hw : w.check = true)
    (hc : r.supportedDegreeCheck w d n shifts = true) {j : ℤ} (hj : j ∈ shifts)
    {q : ℝ} (hq : q ∈ Set.Icc (w.lo : ℝ) (w.hi : ℝ)) :
    0 ≤ r.toReal.residual n j q := by
  have h := Bool.and_eq_true_iff.mp hc
  exact r.checked_state_sound w d n j hr hw h.1 (List.all_eq_true.mp h.2 j hj) hq

#print axioms RationalRow.supportedDegreeCheck_sound
end ForestUnimodality.FiniteKernelRationalCertificate
