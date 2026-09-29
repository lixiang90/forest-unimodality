import ForestUnimodality.FiniteKernelIntervalCertificate
import ForestUnimodality.BinomialMassIntervalCertificate

/-! A complete finite-degree certificate whose probability enclosures are
themselves checked against the genuine binomial law. Only the real q-domain
remains as a hypothesis in the interpretation theorem. -/
namespace ForestUnimodality.BinomialMassIntervalCertificate

open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate

def Table.lowerInt {n : ℕ} (t : Table n) (j : ℤ) : ℚ :=
  if 0 ≤ j ∧ j ≤ n then t.lower j.toNat else 0

def Table.upperInt {n : ℕ} (t : Table n) (j : ℤ) : ℚ :=
  if 0 ≤ j ∧ j ≤ n then t.upper j.toNat else 0

theorem Table.integer_sound {n : ℕ} (t : Table n) (q : ℚ) (h : t.check q = true) (j : ℤ) :
    t.lowerInt j ≤ mass n j q ∧ mass n j q ≤ t.upperInt j := by
  by_cases hj : 0 ≤ j ∧ j ≤ n
  · have hn : j.toNat ≤ n := by omega
    have he : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj.1
    have hb := t.check_sound h j.toNat hn
    simpa only [lowerInt, upperInt, if_pos hj, he] using hb
  · simp [lowerInt, upperInt, mass, hj]

structure ProbabilityDegreeWitness (n : ℕ) where
  curvature : DegreeWitness
  baseA : ℚ
  baseB : ℚ
  tableA : Table n
  tableB : Table n

def ProbabilityDegreeWitness.check {ι : Type*} {n : ℕ} (d : ProbabilityDegreeWitness n)
    (r : RationalRow ι) (w : IntervalWitness) : Bool :=
  d.tableA.check w.lo && d.tableB.check w.hi &&
  r.roundedDegreeCheck w d.curvature n d.baseA d.baseB
    d.tableA.lowerInt d.tableA.upperInt d.tableB.lowerInt d.tableB.upperInt

theorem ProbabilityDegreeWitness.check_sound {ι : Type*} [DecidableEq ι] {n : ℕ}
    (d : ProbabilityDegreeWitness n) (r : RationalRow ι) (w : IntervalWitness)
    (hr : r.signCheck = true) (hw : w.check = true) (hd : d.check r w = true)
    (j : ℤ) {q : ℝ} (hq : q ∈ Set.Icc (w.lo : ℝ) (w.hi : ℝ)) :
    0 ≤ r.toReal.residual n j q := by
  have hp : d.tableA.check w.lo = true ∧ d.tableB.check w.hi = true ∧
      r.roundedDegreeCheck w d.curvature n d.baseA d.baseB
        d.tableA.lowerInt d.tableA.upperInt d.tableB.lowerInt d.tableB.upperInt = true := by
    simpa only [check, Bool.and_eq_true_iff, and_assoc] using hd
  exact r.roundedDegreeCheck_sound w d.curvature n d.baseA d.baseB
    d.tableA.lowerInt d.tableA.upperInt d.tableB.lowerInt d.tableB.upperInt hr hw hp.2.2
    (fun j => (d.tableA.integer_sound w.lo hp.1 j).1)
    (fun j => (d.tableA.integer_sound w.lo hp.1 j).2)
    (fun j => (d.tableB.integer_sound w.hi hp.2.1 j).1)
    (fun j => (d.tableB.integer_sound w.hi hp.2.1 j).2) j hq

#print axioms Table.integer_sound
#print axioms ProbabilityDegreeWitness.check_sound

end ForestUnimodality.BinomialMassIntervalCertificate
