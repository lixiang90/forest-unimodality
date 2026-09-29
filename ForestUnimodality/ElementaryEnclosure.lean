import ForestUnimodality.ExpEnclosure
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Exact log and square-root enclosures. Log endpoints are certified through
proved exponential enclosures; square-root endpoints are checked by squaring
nonnegative rational numbers. -/

namespace ForestUnimodality.ElementaryEnclosure

open ExpEnclosure

structure LogCertificate where
  lowerExp : PowerCertificate
  upperExp : PowerCertificate
  lowerExpLo : ℚ
  lowerExpHi : ℚ
  upperExpLo : ℚ
  upperExpHi : ℚ
  deriving Repr

def LogCertificate.Accepts (cert : LogCertificate) (q lo hi : ℚ) : Prop :=
  0 < q ∧
  cert.lowerExp.check lo cert.lowerExpLo cert.lowerExpHi = true ∧
  cert.upperExp.check hi cert.upperExpLo cert.upperExpHi = true ∧
  cert.lowerExpHi ≤ q ∧ q ≤ cert.upperExpLo

instance (cert : LogCertificate) (q lo hi : ℚ) : Decidable (cert.Accepts q lo hi) := by
  unfold LogCertificate.Accepts
  infer_instance

def LogCertificate.check (cert : LogCertificate) (q lo hi : ℚ) : Bool :=
  decide (cert.Accepts q lo hi)

theorem LogCertificate.check_sound (cert : LogCertificate) {q lo hi : ℚ}
    (hcheck : cert.check q lo hi = true) :
    (lo : ℝ) ≤ Real.log (q : ℝ) ∧ Real.log (q : ℝ) ≤ (hi : ℝ) := by
  have h : cert.Accepts q lo hi := of_decide_eq_true hcheck
  obtain ⟨hq, hL, hU, hlow, hupp⟩ := h
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hLexp := cert.lowerExp.check_sound hL
  have hUexp := cert.upperExp.check_sound hU
  have hlr : (cert.lowerExpHi : ℝ) ≤ q := by exact_mod_cast hlow
  have hur : (q : ℝ) ≤ cert.upperExpLo := by exact_mod_cast hupp
  constructor
  · apply Real.exp_le_exp.mp
    rw [Real.exp_log hqr]
    exact hLexp.2.trans hlr
  · apply Real.exp_le_exp.mp
    rw [Real.exp_log hqr]
    exact hur.trans hUexp.1

def SqrtAccepts (q lo hi : ℚ) : Prop :=
  0 ≤ q ∧ 0 ≤ lo ∧ 0 ≤ hi ∧ lo ^ 2 ≤ q ∧ q ≤ hi ^ 2

instance (q lo hi : ℚ) : Decidable (SqrtAccepts q lo hi) := by
  unfold SqrtAccepts
  infer_instance

def sqrtCheck (q lo hi : ℚ) : Bool := decide (SqrtAccepts q lo hi)

theorem sqrtCheck_sound {q lo hi : ℚ} (hcheck : sqrtCheck q lo hi = true) :
    (lo : ℝ) ≤ Real.sqrt (q : ℝ) ∧ Real.sqrt (q : ℝ) ≤ (hi : ℝ) := by
  have h : SqrtAccepts q lo hi := of_decide_eq_true hcheck
  obtain ⟨hq, hlo, hhi, hl2, hh2⟩ := h
  have hqr : (0 : ℝ) ≤ q := by exact_mod_cast hq
  have hlr : (0 : ℝ) ≤ lo := by exact_mod_cast hlo
  have hhr : (0 : ℝ) ≤ hi := by exact_mod_cast hhi
  have hlr2 : (lo : ℝ) ^ 2 ≤ q := by exact_mod_cast hl2
  have hhr2 : (q : ℝ) ≤ (hi : ℝ) ^ 2 := by exact_mod_cast hh2
  have hs := Real.sq_sqrt hqr
  have hsn := Real.sqrt_nonneg (q : ℝ)
  constructor <;> nlinarith

#print axioms LogCertificate.check_sound
#print axioms sqrtCheck_sound

end ForestUnimodality.ElementaryEnclosure
