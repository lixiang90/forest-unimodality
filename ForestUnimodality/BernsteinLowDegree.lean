import ForestUnimodality.BernsteinPoint

/-! Closed coefficient identities for quadratic interval certificates.
The conclusion remains the original executable Bernstein interval checker. -/
namespace ForestUnimodality.BernsteinCertificate
open PolynomialList

def quadraticPart (p : RatPolynomial) : RatPolynomial :=
  ⟨[p.coeffs.getD 0 0, p.coeffs.getD 1 0, p.coeffs.getD 2 0]⟩

def quadraticIntervalCheck (p : RatPolynomial) (lo hi : ℚ) (c : Fin 3 → ℚ) : Bool :=
  let a := p.coeffs.getD 0 0
  let b := p.coeffs.getD 1 0
  let d := p.coeffs.getD 2 0
  decide (lo ≤ hi) && equalCheck ratZero p (quadraticPart p) &&
    decide ((∀ i, 0 ≤ c i) ∧
      c 0 = a + b*lo + d*lo^2 ∧
      2*c 1 = 2*a + b*(lo+hi) + 2*d*lo*hi ∧
      c 2 = a + b*hi + d*hi^2)

theorem evalReal_expansion_quadratic (c : Fin 3 → ℚ) (x : ℝ) :
    evalReal (expansion ⟨2,c⟩) x =
      (c 0:ℝ)*(1-x)^2 + 2*(c 1:ℝ)*x*(1-x) + (c 2:ℝ)*x^2 := by
  change evalReal (C (c 0)*basis 2 0 + (C (c 1)*basis 2 1 +
    (C (c 2)*basis 2 2 + 0))) x = _
  simp only [evalReal, eval_add, eval_mul, eval_C, eval_zero, basis,
    eval_pow, eval_X, eval_sub, eval_one]
  norm_num [rationalEvaluation]
  ring

theorem intervalCheck_of_quadraticIntervalCheck {p : RatPolynomial} {lo hi : ℚ}
    {c : Fin 3 → ℚ} (h : quadraticIntervalCheck p lo hi c = true) :
    intervalCheck p lo hi ⟨2,c⟩ = true := by
  have hh : lo ≤ hi ∧ equalCheck ratZero p (quadraticPart p) = true ∧
      ((∀ i, 0 ≤ c i) ∧
      c 0 = p.coeffs.getD 0 0 + p.coeffs.getD 1 0*lo + p.coeffs.getD 2 0*lo^2 ∧
      2*c 1 = 2*p.coeffs.getD 0 0 + p.coeffs.getD 1 0*(lo+hi) + 2*p.coeffs.getD 2 0*lo*hi ∧
      c 2 = p.coeffs.getD 0 0 + p.coeffs.getD 1 0*hi + p.coeffs.getD 2 0*hi^2) := by
    simpa only [quadraticIntervalCheck, Bool.and_eq_true_iff, decide_eq_true_eq, and_assoc] using h
  rcases hh with ⟨horder,hpoly,hpos,h0,h1,h2⟩
  have heval (x : ℝ) : evalReal p x =
      (p.coeffs.getD 0 0:ℝ) + (p.coeffs.getD 1 0:ℝ)*x + (p.coeffs.getD 2 0:ℝ)*x^2 := by
    have he := equalCheck_sound rationalEvaluation ratZero ratZero_sound hpoly x
    change evalReal p x = evalReal (quadraticPart p) x at he
    rw [he]
    simp only [quadraticPart, evalReal, eval, evalList, rationalEvaluation]
    ring
  have hc0 : (c 0:ℝ) = (p.coeffs.getD 0 0:ℝ) + (p.coeffs.getD 1 0:ℝ)*(lo:ℝ) +
      (p.coeffs.getD 2 0:ℝ)*(lo:ℝ)^2 := by exact_mod_cast h0
  have hc1 : (c 1:ℝ) = ((2:ℝ)*(p.coeffs.getD 0 0:ℝ) +
      (p.coeffs.getD 1 0:ℝ)*((lo:ℝ)+(hi:ℝ)) +
      2*(p.coeffs.getD 2 0:ℝ)*(lo:ℝ)*(hi:ℝ))/2 := by
    have hh : (2:ℝ)*(c 1:ℝ) = 2*(p.coeffs.getD 0 0:ℝ) +
      (p.coeffs.getD 1 0:ℝ)*((lo:ℝ)+(hi:ℝ)) +
      2*(p.coeffs.getD 2 0:ℝ)*(lo:ℝ)*(hi:ℝ) := by exact_mod_cast h1
    linarith
  have hc2 : (c 2:ℝ) = (p.coeffs.getD 0 0:ℝ) + (p.coeffs.getD 1 0:ℝ)*(hi:ℝ) +
      (p.coeffs.getD 2 0:ℝ)*(hi:ℝ)^2 := by exact_mod_cast h2
  apply Bool.and_eq_true_iff.mpr
  refine ⟨decide_eq_true_eq.mpr horder, ?_⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, decide_eq_true_eq.mpr hpos⟩
  apply equalCheck_of_eval_eq
  intro x
  change evalReal (comp p (affine lo hi)) x = evalReal (expansion ⟨2,c⟩) x
  rw [evalReal_comp_affine, heval, evalReal_expansion_quadratic, hc0, hc1, hc2]
  ring

#print axioms evalReal_expansion_quadratic
#print axioms intervalCheck_of_quadraticIntervalCheck
end ForestUnimodality.BernsteinCertificate
