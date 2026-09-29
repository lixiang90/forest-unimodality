import ForestUnimodality.BernsteinConstant

/-! A singleton interval needs one exact rational evaluation, rather than an
expanded affine pullback and Bernstein basis. The original checker is proved. -/
namespace ForestUnimodality.PolynomialList

theorem zeroCheck_of_toPolynomial_zero {p : Poly ℚ} (h : toPolynomial p = 0) :
    zeroCheck (fun a : ℚ => decide (a = 0)) p = true := by
  rcases p with ⟨cs⟩
  induction cs with
  | nil => rfl
  | cons a cs ih =>
    change Polynomial.C a + Polynomial.X * toPolynomial ⟨cs⟩ = 0 at h
    have ha : a = 0 := by
      simpa using congrArg (Polynomial.eval 0) h
    have ht : toPolynomial ⟨cs⟩ = 0 := by
      have hx : (Polynomial.X : Polynomial ℚ) * toPolynomial ⟨cs⟩ = 0 := by
        simpa only [ha, Polynomial.C_0, zero_add] using h
      exact (mul_eq_zero.mp hx).resolve_left Polynomial.X_ne_zero
    change (decide (a = 0) && zeroCheck (fun a : ℚ => decide (a = 0)) ⟨cs⟩) = true
    simp only [ha, decide_true, Bool.true_and]
    exact ih ht

theorem equalCheck_of_eval_eq {p q : Poly ℚ}
    (h : ∀ x : ℝ, eval rationalEvaluation.value x p = eval rationalEvaluation.value x q) :
    equalCheck (fun a : ℚ => decide (a = 0)) p q = true := by
  apply zeroCheck_of_toPolynomial_zero
  letI : Infinite ℝ := Infinite.of_injective (fun n : ℕ => (n : ℝ)) Nat.cast_injective
  apply Polynomial.map_injective (f := Rat.castHom ℝ) Rat.cast_injective
  apply Polynomial.funext
  intro x
  rw [Polynomial.eval_map, Polynomial.eval_map, eval_toPolynomial, Polynomial.eval₂_zero,
    eval_sub, h x]
  exact sub_self _

end ForestUnimodality.PolynomialList

namespace ForestUnimodality.BernsteinCertificate
open PolynomialList

def evalRat (p : RatPolynomial) (x : ℚ) : ℚ :=
  p.coeffs.foldr (fun a y => a + x * y) 0

theorem evalReal_at_rat (p : RatPolynomial) (x : ℚ) :
    evalReal p (x : ℝ) = (evalRat p x : ℝ) := by
  rcases p with ⟨cs⟩
  induction cs with
  | nil => simp [evalReal, eval, evalList, evalRat]
  | cons a cs ih =>
    change (a : ℝ) + (x : ℝ) * evalReal ⟨cs⟩ (x : ℝ) =
      ((a + x * evalRat ⟨cs⟩ x : ℚ) : ℝ)
    rw [ih, Rat.cast_add, Rat.cast_mul]

def pointCheck (p : RatPolynomial) (x : ℚ) (c : Certificate) : Bool :=
  decide (0 ≤ evalRat p x ∧ ∀ i, c.coeff i = evalRat p x)

theorem intervalCheck_of_pointCheck {p : RatPolynomial} {x : ℚ} {c : Certificate}
    (h : pointCheck p x c = true) : intervalCheck p x x c = true := by
  have hh : 0 ≤ evalRat p x ∧ ∀ i, c.coeff i = evalRat p x := of_decide_eq_true h
  rcases c with ⟨n, coeff⟩
  have hc : coeff = fun _ => evalRat p x := funext hh.2
  subst coeff
  apply Bool.and_eq_true_iff.mpr
  refine ⟨by simp, ?_⟩
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply equalCheck_of_eval_eq
    intro t
    change evalReal (comp p (affine x x)) t = evalReal (expansion ⟨n, fun _ => evalRat p x⟩) t
    rw [evalReal_comp_affine, sub_self, zero_mul, add_zero, evalReal_at_rat,
      evalReal_expansion_constant]
  · apply decide_eq_true_eq.mpr
    intro i
    exact hh.1

#print axioms PolynomialList.equalCheck_of_eval_eq
#print axioms intervalCheck_of_pointCheck
end ForestUnimodality.BernsteinCertificate
