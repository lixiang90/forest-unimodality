import ForestUnimodality.BernsteinCertificate
import Mathlib.Algebra.BigOperators.Fin

/-! Equal Bernstein coefficients represent a constant, in every degree.
Degree-zero certificates can therefore express the same polynomial without
expanding a sum of higher-degree basis polynomials. -/
namespace ForestUnimodality.BernsteinCertificate
open PolynomialList

theorem constant_basis_sum (n : ℕ) (a x : ℝ) :
    (∑ i ∈ Finset.range (n+1), a*(n.choose i:ℝ)*x^i*(1-x)^(n-i))=a := by
  calc
    _ = a*(x+(1-x))^n := by
      rw [add_pow,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = a := by simp

theorem evalReal_expansion_constant (n : ℕ) (a : ℚ) (x : ℝ) :
    evalReal (expansion ⟨n,fun _=>a⟩) x=(a:ℝ) := by
  calc
    _ = ((List.finRange (n+1)).map (fun i : Fin (n+1)=>
        (a:ℝ)*(n.choose (i:ℕ):ℝ)*x^(i:ℕ)*(1-x)^(n-(i:ℕ)))).sum := by
      simp only [evalReal,expansion,eval_sum,List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      change evalReal (C a*basis n (i:ℕ)) x=_
      simp only [evalReal,basis,eval_mul,eval_C,eval_pow,eval_X,eval_sub,eval_one]
      simp only [rationalEvaluation,Rat.cast_natCast]
      ring
    _ = (a:ℝ) := by
      rw [←Fin.sum_univ_def]
      exact (Fin.sum_univ_eq_sum_range
        (fun i : ℕ=>(a:ℝ)*(n.choose i:ℝ)*x^i*(1-x)^(n-i)) (n+1)).trans
        (constant_basis_sum n a x)

#print axioms constant_basis_sum
#print axioms evalReal_expansion_constant
end ForestUnimodality.BernsteinCertificate
