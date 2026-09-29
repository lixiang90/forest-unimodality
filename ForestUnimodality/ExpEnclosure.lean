import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Exact rational exponential enclosures. The exporter may propose rational
endpoints, but acceptance checks a proved Taylor remainder. No floating-point
evaluation of exp is part of the trusted proof. -/

namespace ForestUnimodality.ExpEnclosure
open Finset

def taylorSum (q : ℚ) (n : ℕ) : ℚ := ∑ i ∈ range n, q ^ i / (i.factorial : ℚ)

def error (q : ℚ) (n : ℕ) : ℚ :=
  |q| ^ n * ((n + 1 : ℕ) : ℚ) / ((n.factorial : ℚ) * n)

def SmallAccepts (q : ℚ) (n : ℕ) (lo hi : ℚ) : Prop :=
  -1 ≤ q ∧ q ≤ 1 ∧ 0 < n ∧ lo ≤ taylorSum q n - error q n ∧ taylorSum q n + error q n ≤ hi

instance (q : ℚ) (n : ℕ) (lo hi : ℚ) : Decidable (SmallAccepts q n lo hi) := by
  unfold SmallAccepts
  infer_instance

def smallCheck (q : ℚ) (n : ℕ) (lo hi : ℚ) : Bool := decide (SmallAccepts q n lo hi)

theorem cast_taylorSum (q : ℚ) (n : ℕ) : (taylorSum q n : ℝ) =
    ∑ i ∈ range n, (q : ℝ) ^ i / (i.factorial : ℝ) := by
  simp [taylorSum]

theorem cast_error (q : ℚ) (n : ℕ) : (error q n : ℝ) =
    |(q : ℝ)| ^ n * ((n + 1 : ℕ) : ℝ) / ((n.factorial : ℝ) * n) := by
  simp [error]

theorem smallCheck_sound {q lo hi : ℚ} {n : ℕ}
    (hcheck : smallCheck q n lo hi = true) :
    (lo : ℝ) ≤ Real.exp (q : ℝ) ∧ Real.exp (q : ℝ) ≤ (hi : ℝ) := by
  have h : SmallAccepts q n lo hi := of_decide_eq_true hcheck
  obtain ⟨hqlo, hqhi, hn, hlo, hhi⟩ := h
  have hq : |(q : ℝ)| ≤ 1 := abs_le.mpr ⟨by exact_mod_cast hqlo, by exact_mod_cast hqhi⟩
  have hb := Real.exp_bound hq hn
  have hl : (lo : ℝ) ≤ (taylorSum q n : ℝ) - (error q n : ℝ) := by exact_mod_cast hlo
  have hh : (taylorSum q n : ℝ) + (error q n : ℝ) ≤ (hi : ℝ) := by exact_mod_cast hhi
  have herr : |Real.exp (q : ℝ) - (taylorSum q n : ℝ)| ≤ (error q n : ℝ) := by
    simpa only [cast_taylorSum, cast_error, Nat.succ_eq_add_one, mul_div_assoc] using hb
  obtain ⟨he1, he2⟩ := abs_le.mp herr
  constructor <;> linarith

/-- Scaling a small argument allows arbitrary signed rational arguments. -/
structure PowerCertificate where
  parts : ℕ
  inner : ℚ
  terms : ℕ
  innerLo : ℚ
  innerHi : ℚ
  deriving Repr

def PowerCertificate.Accepts (cert : PowerCertificate) (q lo hi : ℚ) : Prop :=
  q = cert.parts * cert.inner ∧
  smallCheck cert.inner cert.terms cert.innerLo cert.innerHi = true ∧
  0 ≤ cert.innerLo ∧ lo ≤ cert.innerLo ^ cert.parts ∧ cert.innerHi ^ cert.parts ≤ hi

instance (cert : PowerCertificate) (q lo hi : ℚ) : Decidable (cert.Accepts q lo hi) := by
  unfold PowerCertificate.Accepts
  infer_instance

def PowerCertificate.check (cert : PowerCertificate) (q lo hi : ℚ) : Bool :=
  decide (cert.Accepts q lo hi)

theorem exp_nat_mul (x : ℝ) (n : ℕ) : Real.exp ((n : ℝ) * x) = (Real.exp x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add_one, add_mul, one_mul, Real.exp_add, ih, pow_succ]

theorem PowerCertificate.check_sound (cert : PowerCertificate) {q lo hi : ℚ}
    (hcheck : cert.check q lo hi = true) :
    (lo : ℝ) ≤ Real.exp (q : ℝ) ∧ Real.exp (q : ℝ) ≤ (hi : ℝ) := by
  have h : cert.Accepts q lo hi := of_decide_eq_true hcheck
  obtain ⟨hq, hs, hnonneg, hlo, hhi⟩ := h
  have he := smallCheck_sound hs
  have hq' : (q : ℝ) = (cert.parts : ℝ) * (cert.inner : ℝ) := by exact_mod_cast hq
  rw [hq', exp_nat_mul]
  have hlow : (0 : ℝ) ≤ cert.innerLo := by exact_mod_cast hnonneg
  have hl : (lo : ℝ) ≤ (cert.innerLo : ℝ) ^ cert.parts := by exact_mod_cast hlo
  have hh : (cert.innerHi : ℝ) ^ cert.parts ≤ (hi : ℝ) := by exact_mod_cast hhi
  constructor
  · exact hl.trans (pow_le_pow_left₀ hlow he.1 _)
  · exact (pow_le_pow_left₀ (Real.exp_pos _).le he.2 _).trans hh

#print axioms smallCheck_sound
#print axioms PowerCertificate.check_sound

end ForestUnimodality.ExpEnclosure
