import ForestUnimodality.BernsteinLowDegree

/-! Affine interval certificates are determined by their two endpoint values.
The conclusion remains the original executable Bernstein interval checker. -/
namespace ForestUnimodality.BernsteinCertificate
open PolynomialList

def linearPart (p : RatPolynomial) : RatPolynomial :=
  ⟨[p.coeffs.getD 0 0, p.coeffs.getD 1 0]⟩

def linearIntervalCheck (p : RatPolynomial) (lo hi : ℚ) (c : Fin 2 → ℚ) : Bool :=
  let a := p.coeffs.getD 0 0
  let b := p.coeffs.getD 1 0
  decide (lo ≤ hi) && equalCheck ratZero p (linearPart p) &&
    decide ((∀ i, 0 ≤ c i) ∧ c 0 = a + b*lo ∧ c 1 = a + b*hi)

theorem evalReal_expansion_linear (c : Fin 2 → ℚ) (x : ℝ) :
    evalReal (expansion ⟨1,c⟩) x = (c 0:ℝ)*(1-x) + (c 1:ℝ)*x := by
  change evalReal (C (c 0)*basis 1 0 + (C (c 1)*basis 1 1 + 0)) x = _
  simp only [evalReal, eval_add, eval_mul, eval_C, eval_zero, basis,
    eval_pow, eval_X, eval_sub, eval_one]
  norm_num [rationalEvaluation]

theorem intervalCheck_of_linearIntervalCheck {p : RatPolynomial} {lo hi : ℚ}
    {c : Fin 2 → ℚ} (h : linearIntervalCheck p lo hi c = true) :
    intervalCheck p lo hi ⟨1,c⟩ = true := by
  have hh : lo ≤ hi ∧ equalCheck ratZero p (linearPart p) = true ∧
      ((∀ i, 0 ≤ c i) ∧
      c 0 = p.coeffs.getD 0 0 + p.coeffs.getD 1 0*lo ∧
      c 1 = p.coeffs.getD 0 0 + p.coeffs.getD 1 0*hi) := by
    simpa only [linearIntervalCheck, Bool.and_eq_true_iff, decide_eq_true_eq, and_assoc] using h
  rcases hh with ⟨horder,hpoly,hpos,h0,h1⟩
  have heval (x : ℝ) : evalReal p x =
      (p.coeffs.getD 0 0:ℝ) + (p.coeffs.getD 1 0:ℝ)*x := by
    have he := equalCheck_sound rationalEvaluation ratZero ratZero_sound hpoly x
    change evalReal p x = evalReal (linearPart p) x at he
    rw [he]
    simp only [linearPart, evalReal, eval, evalList, rationalEvaluation]
    ring
  have hc0 : (c 0:ℝ) = (p.coeffs.getD 0 0:ℝ) +
      (p.coeffs.getD 1 0:ℝ)*(lo:ℝ) := by exact_mod_cast h0
  have hc1 : (c 1:ℝ) = (p.coeffs.getD 0 0:ℝ) +
      (p.coeffs.getD 1 0:ℝ)*(hi:ℝ) := by exact_mod_cast h1
  apply Bool.and_eq_true_iff.mpr
  refine ⟨decide_eq_true_eq.mpr horder, ?_⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, decide_eq_true_eq.mpr hpos⟩
  apply equalCheck_of_eval_eq
  intro x
  change evalReal (comp p (affine lo hi)) x = evalReal (expansion ⟨1,c⟩) x
  rw [evalReal_comp_affine, heval, evalReal_expansion_linear, hc0, hc1]
  ring

#print axioms evalReal_expansion_linear
#print axioms intervalCheck_of_linearIntervalCheck
end ForestUnimodality.BernsteinCertificate
