import ForestUnimodality.IntegerCertificate
import Mathlib.Algebra.BigOperators.Fin

/-! Kernel-reducible certificate evaluation. Row support is tested before
binomial coefficients or release envelopes are evaluated. The original checker
and mathematical statement are unchanged. -/

namespace ForestUnimodality.FiniteRows

/-- A support guard that does not evaluate its coefficient on other layers. -/
def kernelSelect (j r : ℕ) (c : ℤ) : ℤ := if j = r then c else 0

theorem kernelSelect_eq (j r : ℕ) (c : ℤ) :
    kernelSelect j r c = indicator j r * c := by
  by_cases h : j = r <;> simp [kernelSelect, indicator, h]

def kernelShiftedChoose (m j r : ℕ) : ℕ :=
  if j ≤ r then Nat.fast_choose m (r - j) else 0

theorem kernelShiftedChoose_eq (m j r : ℕ) :
    kernelShiftedChoose m j r = shiftedChoose m j r := by
  simp only [kernelShiftedChoose, shiftedChoose, Nat.choose_eq_fast_choose]

def kernelDifferenceCoeff (m j r : ℕ) : ℤ :=
  (kernelShiftedChoose m j r : ℤ) - (kernelShiftedChoose m (j + 1) r : ℤ)

theorem kernelDifferenceCoeff_eq (m j r : ℕ) :
    kernelDifferenceCoeff m j r = differenceCoeff m j r := by
  simp only [kernelDifferenceCoeff, differenceCoeff, kernelShiftedChoose_eq]

def kernelCoeff (n a : ℕ) (row : Row) (jm : ℕ × ℕ) : ℤ :=
  let j := jm.1
  let m := jm.2
  let v := n - a
  match row with
  | .count r => kernelSelect j r 1
  | .path r => -(kernelShiftedChoose m j r : ℤ)
  | .privateRow r h =>
      kernelSelect j r (max 0 (((r : ℤ) - 1) * m + a - r + 1 - (r : ℤ) * h)) -
      kernelSelect j (r - 1) ((v - (r - 1) : ℕ) * max 0 ((m : ℤ) - h))
  | .hall r l =>
      kernelSelect j (r + 1) ((r + 1 : ℕ) * (Nat.fast_choose m l : ℤ)) -
      kernelSelect j r ((hallFactor n a r l : ℤ) * (Nat.fast_choose m l : ℤ))
  | .tail r h => kernelSelect j r (deletionThresholdCoeff a r h m : ℤ) -
      kernelSelect j (r - 1) ((v - (r - 1) : ℕ) * (if h ≤ m then 1 else 0))
  | .releaseUpper r h =>
      kernelSelect j (r - 1) ((extensionFactor n a r : ℤ) * max 0 ((m : ℤ) - h)) -
      kernelSelect j r (releaseUpperCoeff a r h m : ℤ)
  | .tailUpper r h =>
      kernelSelect j (r - 1) ((extensionFactor n a r : ℤ) * (if h ≤ m then 1 else 0)) -
      kernelSelect j r (thresholdUpperCoeff a r h m : ℤ)
  | .mean r => kernelSelect j r (-(m : ℤ)) - kernelSelect j 2 (meanBeta n a r)
  | .unionRow r => kernelSelect j r ((a : ℤ) - m) -
      kernelSelect j 1 (((a : ℤ) - m) * (Nat.fast_choose (v - 1) (r - 1) : ℤ))
  | .edgeLower r => kernelSelect j r (-1) +
      kernelSelect j 2 (Nat.fast_choose (v - 2) (r - 2) : ℤ)
  | .edgeUpper r =>
      if intrinsicBudget n a = 0 then kernelSelect j r 1 else
        kernelSelect j r (intrinsicBudget n a : ℤ) -
        kernelSelect j 2 (edgeGap v (intrinsicBudget n a) r : ℤ)
  | .assumptionRow r => kernelDifferenceCoeff m j r

theorem kernelCoeff_eq (n a : ℕ) (row : Row) (jm : ℕ × ℕ) :
    kernelCoeff n a row jm = coeff n a row jm := by
  cases row <;>
    simp only [kernelCoeff, coeff, kernelSelect_eq, kernelShiftedChoose_eq,
      kernelDifferenceCoeff_eq, Nat.choose_eq_fast_choose]
  all_goals try split_ifs
  all_goals ring

/-- Rewriting the original coefficient evaluator to the support-guarded
version is an equality proof, not a new acceptance assumption. -/
theorem coeff_eq_kernelCoeff (n a : ℕ) (row : Row) (jm : ℕ × ℕ) :
    coeff n a row jm = kernelCoeff n a row jm := (kernelCoeff_eq n a row jm).symm

theorem sum_array_rows (rows : Array WeightedRow) (f : WeightedRow → ℤ) :
    (∑ i : Fin rows.size, f rows[i]) = (rows.toList.map f).sum := by
  cases rows with
  | mk xs => exact Fin.sum_univ_fun_getElem xs f

theorem Certificate.residual_eq_kernel (cert : Certificate) (n a k : ℕ) (kind : Kind)
    (jm : ℕ × ℕ) :
    cert.residual n a k kind jm =
      (cert.objectiveScale : ℤ) * targetCoeff k kind jm - cert.eta * indicator jm.1 1 -
        (cert.rows.toList.map (fun wr =>
          (wr.weight : ℤ) * kernelCoeff n a wr.row jm)).sum := by
  unfold Certificate.residual
  rw [sum_array_rows cert.rows (fun wr => (wr.weight : ℤ) * coeff n a wr.row jm)]
  simp only [coeff_eq_kernelCoeff]

theorem Certificate.bound_eq_kernel (cert : Certificate) (n a k : ℕ) (kind : Kind) :
    cert.bound n a k kind =
      (cert.objectiveScale : ℤ) * targetConstant a k kind + cert.eta * (n - a : ℕ) +
        (cert.rows.toList.map (fun wr => (wr.weight : ℤ) * rhs n a wr.row)).sum +
        ∑ j ∈ Finset.Icc 1 (n - a), ((n - a).choose j : ℤ) * cert.cap j := by
  unfold Certificate.bound
  rw [sum_array_rows cert.rows (fun wr => (wr.weight : ℤ) * rhs n a wr.row)]

def rowSupported (row : Row) (j : ℕ) : Prop :=
  match row with
  | .count r => j = r
  | .path r | .assumptionRow r => j ≤ r
  | .privateRow r _ | .tail r _ | .releaseUpper r _ | .tailUpper r _ =>
      j = r ∨ j = r - 1
  | .hall r _ => j = r + 1 ∨ j = r
  | .mean r | .edgeLower r | .edgeUpper r => j = r ∨ j = 2
  | .unionRow r => j = r ∨ j = 1

instance (row : Row) (j : ℕ) : Decidable (rowSupported row j) := by
  unfold rowSupported
  cases row <;> infer_instance

theorem kernelCoeff_zero_of_unsupported (n a : ℕ) (row : Row) (jm : ℕ × ℕ)
    (h : ¬ rowSupported row jm.1) : kernelCoeff n a row jm = 0 := by
  cases row <;>
    simp_all [rowSupported, kernelCoeff, kernelSelect, kernelShiftedChoose,
      kernelDifferenceCoeff]
  omega

def layerRows (rows : List WeightedRow) (j : ℕ) : List WeightedRow :=
  rows.filter (fun wr => decide (rowSupported wr.row j))

theorem sum_layerRows (rows : List WeightedRow) (n a : ℕ) (jm : ℕ × ℕ) :
    ((layerRows rows jm.1).map (fun wr => (wr.weight : ℤ) * kernelCoeff n a wr.row jm)).sum =
      (rows.map (fun wr => (wr.weight : ℤ) * kernelCoeff n a wr.row jm)).sum := by
  induction rows with
  | nil => rfl
  | cons wr rest ih =>
    by_cases h : rowSupported wr.row jm.1
    · simpa [layerRows, h] using congrArg ((wr.weight : ℤ) * kernelCoeff n a wr.row jm + ·) ih
    · have hz := kernelCoeff_zero_of_unsupported n a wr.row jm h
      simpa [layerRows, h, hz] using ih

theorem Certificate.residual_eq_sparse_kernel (cert : Certificate)
    (n a k : ℕ) (kind : Kind) (jm : ℕ × ℕ) :
    cert.residual n a k kind jm =
      (cert.objectiveScale : ℤ) * targetCoeff k kind jm - cert.eta * indicator jm.1 1 -
        ((layerRows cert.rows.toList jm.1).map (fun wr =>
          (wr.weight : ℤ) * kernelCoeff n a wr.row jm)).sum := by
  rw [cert.residual_eq_kernel, sum_layerRows]

def Certificate.kernelResidualCheck (cert : Certificate)
    (n a k : ℕ) (kind : Kind) : Bool :=
  (List.range (min a (n - a))).all fun i =>
    let j := i + 1
    let active := layerRows cert.rows.toList j
    (List.range (a - j + 1)).all fun m =>
      decide ((cert.objectiveScale : ℤ) * targetCoeff k kind (j, m) -
        cert.eta * indicator j 1 -
        (active.map (fun wr => (wr.weight : ℤ) * kernelCoeff n a wr.row (j, m))).sum ≤
        cert.cap j)

theorem Certificate.kernelResidualCheck_eq_true_iff (cert : Certificate)
    (n a k : ℕ) (kind : Kind) :
    cert.kernelResidualCheck n a k kind = true ↔
      ∀ jm ∈ triangularIndices a (n - a), cert.residual n a k kind jm ≤ cert.cap jm.1 := by
  simp only [Certificate.kernelResidualCheck, List.all_eq_true, List.mem_range,
    decide_eq_true_eq]
  constructor
  · intro h ⟨j, m⟩ hjm
    obtain ⟨hj, hjv, hma⟩ := mem_triangularIndices.mp hjm
    have hi : j - 1 < min a (n - a) := by omega
    have heq : j - 1 + 1 = j := by omega
    have h' := h (j - 1) hi
    rw [heq] at h'
    rw [cert.residual_eq_sparse_kernel]
    exact h' m (by omega)
  · intro h i hi m hm
    have hjm : (i + 1, m) ∈ triangularIndices a (n - a) :=
      mem_triangularIndices.mpr ⟨by omega, by omega, by omega⟩
    simpa only [cert.residual_eq_sparse_kernel] using h (i + 1, m) hjm

def Certificate.KernelAccepts (cert : Certificate) (n a k : ℕ) (kind : Kind) : Prop :=
  0 < cert.objectiveScale ∧
  cert.caps.size = n - a + 1 ∧
  (∀ i : Fin cert.rows.size, Valid n a k kind cert.rows[i].row) ∧
  (∀ j ∈ Finset.Icc 1 (n - a), 0 ≤ cert.cap j) ∧
  cert.kernelResidualCheck n a k kind = true ∧
  (if kind = .positive then cert.bound n a k kind < 0 else cert.bound n a k kind ≤ 0)

instance (cert : Certificate) (n a k : ℕ) (kind : Kind) :
    Decidable (cert.KernelAccepts n a k kind) := by
  unfold Certificate.KernelAccepts
  infer_instance

def Certificate.kernelCheck (cert : Certificate) (n a k : ℕ) (kind : Kind) : Bool :=
  decide (cert.KernelAccepts n a k kind)

theorem Certificate.kernelCheck_eq_check (cert : Certificate)
    (n a k : ℕ) (kind : Kind) : cert.kernelCheck n a k kind = cert.check n a k kind := by
  apply Bool.eq_iff_iff.mpr
  simp only [Certificate.kernelCheck, Certificate.check, decide_eq_true_eq,
    Certificate.KernelAccepts, Certificate.Accepts, cert.kernelResidualCheck_eq_true_iff]

/-- Check an explicit certificate by reduction in the Lean kernel. This tactic
only rewrites through the preceding proved equalities, then invokes `decide`.
The caller can choose resource limits appropriate to the certificate size. -/
macro "kernel_certificate" : tactic => `(tactic| (
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel))

#print axioms kernelCoeff_eq
#print axioms Certificate.residual_eq_kernel
#print axioms Certificate.bound_eq_kernel
#print axioms Certificate.residual_eq_sparse_kernel
#print axioms Certificate.kernelCheck_eq_check

end ForestUnimodality.FiniteRows
