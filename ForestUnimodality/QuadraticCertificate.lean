import ForestUnimodality.BernsteinCertificate

/-! Exact rational checks for quadratic nonnegativity on a real half-line.
The endpoint and shifted slope/discriminant checks cover every real point,
including a possible interior vertex; they are not integer sampling tests. -/

namespace ForestUnimodality.QuadraticCertificate

open PolynomialList BernsteinCertificate

def quadratic (A B C : ℚ) : RatPolynomial := ⟨[C, B, A]⟩

def rayCheck (A B C bound : ℚ) : Bool :=
  decide (0 ≤ A ∧ 0 ≤ A * bound ^ 2 + B * bound + C ∧
    (0 ≤ 2 * A * bound + B ∨
      (2 * A * bound + B) ^ 2 ≤ 4 * A * (A * bound ^ 2 + B * bound + C)))

/-- Complete coefficient equality is checked before the half-line test. -/
def check (p : RatPolynomial) (A B C bound : ℚ) : Bool :=
  equalCheck ratZero p (quadratic A B C) && rayCheck A B C bound

theorem quadratic_nonneg_on_nonneg {a b c t : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hb : 0 ≤ b ∨ b ^ 2 ≤ 4 * a * c) (ht : 0 ≤ t) :
    0 ≤ a * t ^ 2 + b * t + c := by
  rcases hb with hb | hd
  · exact add_nonneg (add_nonneg (mul_nonneg ha (sq_nonneg t)) (mul_nonneg hb ht)) hc
  · by_cases hzero : a = 0
    · have hbzero : b = 0 := by rw [hzero] at hd; nlinarith [sq_nonneg b]
      simpa only [hzero, hbzero, zero_mul, zero_add] using hc
    · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hzero)
      have hmul : 0 ≤ 4 * a * (a * t ^ 2 + b * t + c) := by
        nlinarith only [hd, sq_nonneg (2 * a * t + b)]
      exact nonneg_of_mul_nonneg_right hmul (by positivity)

theorem evalReal_quadratic (A B C : ℚ) (x : ℝ) :
    evalReal (quadratic A B C) x = (A : ℝ) * x ^ 2 + (B : ℝ) * x + C := by
  simp only [evalReal, quadratic, eval, evalList, rationalEvaluation]
  ring

theorem rayCheck_sound {A B C bound : ℚ} (h : rayCheck A B C bound = true)
    {x : ℝ} (hx : (bound : ℝ) ≤ x) : 0 ≤ evalReal (quadratic A B C) x := by
  have hQ : 0 ≤ A ∧ 0 ≤ A * bound ^ 2 + B * bound + C ∧
      (0 ≤ 2 * A * bound + B ∨
        (2 * A * bound + B) ^ 2 ≤ 4 * A * (A * bound ^ 2 + B * bound + C)) :=
    of_decide_eq_true h
  have hR : (0 : ℝ) ≤ A ∧ 0 ≤ (A : ℝ) * (bound : ℝ) ^ 2 + (B : ℝ) * bound + C ∧
      (0 ≤ 2 * (A : ℝ) * bound + B ∨
        (2 * (A : ℝ) * bound + B) ^ 2 ≤
          4 * (A : ℝ) * ((A : ℝ) * (bound : ℝ) ^ 2 + (B : ℝ) * bound + C)) := by
    exact_mod_cast hQ
  have hp := quadratic_nonneg_on_nonneg hR.1 hR.2.1 hR.2.2 (sub_nonneg.mpr hx)
  rw [evalReal_quadratic]
  convert hp using 1
  ring

theorem check_sound {p : RatPolynomial} {A B C bound : ℚ}
    (h : check p A B C bound = true) {x : ℝ} (hx : (bound : ℝ) ≤ x) :
    0 ≤ evalReal p x := by
  have hc : equalCheck ratZero p (quadratic A B C) = true ∧ rayCheck A B C bound = true := by
    simpa only [check, Bool.and_eq_true_iff] using h
  rw [evalReal, equalCheck_sound rationalEvaluation ratZero ratZero_sound hc.1 x]
  exact rayCheck_sound hc.2 hx

/-- Reflection gives the opposite real half-line without changing the
discriminant argument or truncating the variable. -/
def leftRayCheck (A B C bound : ℚ) : Bool := rayCheck A (-B) C (-bound)

theorem leftRayCheck_sound {A B C bound : ℚ} (h : leftRayCheck A B C bound = true)
    {x : ℝ} (hx : x ≤ (bound : ℝ)) : 0 ≤ evalReal (quadratic A B C) x := by
  have hx' : ((-bound : ℚ) : ℝ) ≤ -x := by push_cast; linarith
  have hp := rayCheck_sound h hx'
  rw [evalReal_quadratic] at hp ⊢
  push_cast at hp
  nlinarith

theorem check_polynomial_sound {p : RatPolynomial} {A B C bound : ℚ}
    (h : check p A B C bound = true) {x : ℝ} (hx : (bound : ℝ) ≤ x) :
    0 ≤ (toPolynomial p).eval₂ (Rat.castHom ℝ) x := by
  rw [eval_toPolynomial]
  exact check_sound h hx

/-- The discriminant branch accepts an interior zero at x=3 on [2,∞). -/
theorem interior_vertex_checked : check ⟨[9, -6, 1]⟩ 1 (-6) 9 2 = true := by decide +kernel

/-- Nonnegative endpoint values alone do not accept a negative interior vertex. -/
theorem negative_vertex_rejected : check ⟨[8, -6, 1]⟩ 1 (-6) 8 2 = false := by decide +kernel

/-- The slope branch handles affine tails without dividing by the quadratic coefficient. -/
theorem affine_tail_checked : check ⟨[-6, 2]⟩ 0 2 (-6) 3 = true := by decide +kernel

#print axioms rayCheck_sound
#print axioms check_sound
#print axioms leftRayCheck_sound
#print axioms interior_vertex_checked
#print axioms negative_vertex_rejected

end ForestUnimodality.QuadraticCertificate
