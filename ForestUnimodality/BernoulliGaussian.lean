import ForestUnimodality.BinomialFourier
import ForestUnimodality.TriangularGaussian
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Exact Bernoulli modulus and a full-period Gaussian envelope. The endpoint
variance comparison uses finite Taylor inequalities and a rational polynomial
identity on `[0,10]`; no sampled or asymptotic estimate is assumed. -/
namespace ForestUnimodality
open Real Set

theorem centeredBernoulliCharacteristic_norm (q t : ℝ) :
    ‖centeredBernoulliCharacteristic q t‖ =
      ‖((1 - q : ℝ) : ℂ) + (q : ℂ) * Complex.exp ((t : ℂ) * Complex.I)‖ := by
  unfold centeredBernoulliCharacteristic
  rw [norm_mul, Complex.norm_exp]
  simp

theorem centeredBernoulliCharacteristic_norm_sq (q t : ℝ) :
    ‖centeredBernoulliCharacteristic q t‖ ^ 2 =
      1 - 2 * (q * (1 - q)) * (1 - Real.cos t) := by
  rw [centeredBernoulliCharacteristic_norm, Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.exp_mul_I, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.ofReal_re]
  have h := Real.sin_sq_add_cos_sq t
  have hh := congrArg (fun a : ℝ => q ^ 2 * a) h
  nlinarith

private theorem nonneg_of_deriv {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hzero : 0 ≤ f 0)
    (hd : ∀ x, 0 < x → 0 ≤ deriv f x) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hm := monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
    hf.continuous.continuousOn hf.differentiableOn
    (fun x hx => hd x (by simpa using hx))
  exact hzero.trans (hm (by simp) hx hx)

theorem cos_le_taylor_twelve {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 +
      x ^ 8 / 40320 - x ^ 10 / 3628800 + x ^ 12 / 479001600 := by
  have h9 (t : ℝ) (ht : 0 ≤ t) :
      0 ≤ t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 - Real.sin t := by
    apply nonneg_of_deriv (f := fun t =>
      t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 - Real.sin t)
      (by fun_prop) (by norm_num) ?_ ht
    intro y hy
    have he := TriangularGaussian.cos_le_taylor_eight hy.le
    simp (disch := fun_prop)
    linarith
  have h10 (t : ℝ) (ht : 0 ≤ t) :
      0 ≤ Real.cos t - 1 + t ^ 2 / 2 - t ^ 4 / 24 + t ^ 6 / 720 -
        t ^ 8 / 40320 + t ^ 10 / 3628800 := by
    apply nonneg_of_deriv (f := fun t =>
      Real.cos t - 1 + t ^ 2 / 2 - t ^ 4 / 24 + t ^ 6 / 720 -
        t ^ 8 / 40320 + t ^ 10 / 3628800)
      (by fun_prop) (by norm_num) ?_ ht
    intro y hy
    have he := h9 y hy.le
    simp (disch := fun_prop)
    linarith
  have h11 (t : ℝ) (ht : 0 ≤ t) :
      0 ≤ Real.sin t - t + t ^ 3 / 6 - t ^ 5 / 120 + t ^ 7 / 5040 -
        t ^ 9 / 362880 + t ^ 11 / 39916800 := by
    apply nonneg_of_deriv (f := fun t =>
      Real.sin t - t + t ^ 3 / 6 - t ^ 5 / 120 + t ^ 7 / 5040 -
        t ^ 9 / 362880 + t ^ 11 / 39916800)
      (by fun_prop) (by norm_num) ?_ ht
    intro y hy
    have he := h10 y hy.le
    simp (disch := fun_prop)
    linarith
  have h12 : 0 ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 +
      x ^ 8 / 40320 - x ^ 10 / 3628800 + x ^ 12 / 479001600 - Real.cos x := by
    apply nonneg_of_deriv (f := fun t =>
      1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 +
        t ^ 8 / 40320 - t ^ 10 / 3628800 + t ^ 12 / 479001600 - Real.cos t)
      (by fun_prop) (by norm_num) ?_ hx
    intro y hy
    have he := h11 y hy.le
    simp (disch := fun_prop)
    linarith
  linarith

theorem exp_neg_ge_taylor_nine {x : ℝ} (hx : 0 ≤ x) :
    1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 - x ^ 5 / 120 +
      x ^ 6 / 720 - x ^ 7 / 5040 + x ^ 8 / 40320 - x ^ 9 / 362880 ≤ Real.exp (-x) := by
  have h5 (t : ℝ) (ht : 0 ≤ t) :
      0 ≤ Real.exp (-t) - 1 + t - t ^ 2 / 2 + t ^ 3 / 6 - t ^ 4 / 24 + t ^ 5 / 120 := by
    apply nonneg_of_deriv (f := fun t =>
      Real.exp (-t) - 1 + t - t ^ 2 / 2 + t ^ 3 / 6 - t ^ 4 / 24 + t ^ 5 / 120)
      (by fun_prop) (by norm_num) ?_ ht
    intro y hy
    have he := TriangularGaussian.exp_neg_le_taylor_four hy.le
    simp (disch := fun_prop)
    linarith
  have h6 (t : ℝ) (ht : 0 ≤ t) :
      0 ≤ 1 - t + t ^ 2 / 2 - t ^ 3 / 6 + t ^ 4 / 24 - t ^ 5 / 120 + t ^ 6 / 720 - Real.exp (-t) := by
    apply nonneg_of_deriv (f := fun t =>
      1 - t + t ^ 2 / 2 - t ^ 3 / 6 + t ^ 4 / 24 - t ^ 5 / 120 + t ^ 6 / 720 - Real.exp (-t))
      (by fun_prop) (by norm_num) ?_ ht
    intro y hy
    have he := h5 y hy.le
    simp (disch := fun_prop)
    linarith
  have h7 (t : ℝ) (ht : 0 ≤ t) :
      0 ≤ Real.exp (-t) - 1 + t - t ^ 2 / 2 + t ^ 3 / 6 - t ^ 4 / 24 +
        t ^ 5 / 120 - t ^ 6 / 720 + t ^ 7 / 5040 := by
    apply nonneg_of_deriv (f := fun t =>
      Real.exp (-t) - 1 + t - t ^ 2 / 2 + t ^ 3 / 6 - t ^ 4 / 24 +
        t ^ 5 / 120 - t ^ 6 / 720 + t ^ 7 / 5040)
      (by fun_prop) (by norm_num) ?_ ht
    intro y hy
    have he := h6 y hy.le
    simp (disch := fun_prop)
    linarith
  have h8 (t : ℝ) (ht : 0 ≤ t) :
      0 ≤ 1 - t + t ^ 2 / 2 - t ^ 3 / 6 + t ^ 4 / 24 - t ^ 5 / 120 +
        t ^ 6 / 720 - t ^ 7 / 5040 + t ^ 8 / 40320 - Real.exp (-t) := by
    apply nonneg_of_deriv (f := fun t =>
      1 - t + t ^ 2 / 2 - t ^ 3 / 6 + t ^ 4 / 24 - t ^ 5 / 120 +
        t ^ 6 / 720 - t ^ 7 / 5040 + t ^ 8 / 40320 - Real.exp (-t))
      (by fun_prop) (by norm_num) ?_ ht
    intro y hy
    have he := h7 y hy.le
    simp (disch := fun_prop)
    linarith
  have h9 : 0 ≤ Real.exp (-x) - 1 + x - x ^ 2 / 2 + x ^ 3 / 6 - x ^ 4 / 24 +
      x ^ 5 / 120 - x ^ 6 / 720 + x ^ 7 / 5040 - x ^ 8 / 40320 + x ^ 9 / 362880 := by
    apply nonneg_of_deriv (f := fun t =>
      Real.exp (-t) - 1 + t - t ^ 2 / 2 + t ^ 3 / 6 - t ^ 4 / 24 +
        t ^ 5 / 120 - t ^ 6 / 720 + t ^ 7 / 5040 - t ^ 8 / 40320 + t ^ 9 / 362880)
      (by fun_prop) (by norm_num) ?_ hx
    intro y hy
    have he := h8 y hy.le
    simp (disch := fun_prop)
    linarith
  linarith

private noncomputable def expPolynomial (x : ℝ) : ℝ :=
  1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 - x ^ 5 / 120 +
    x ^ 6 / 720 - x ^ 7 / 5040 + x ^ 8 / 40320 - x ^ 9 / 362880

private noncomputable def cosPolynomial (x : ℝ) : ℝ :=
  1 - x / 2 + x ^ 2 / 24 - x ^ 3 / 720 + x ^ 4 / 40320 -
    x ^ 5 / 3628800 + x ^ 6 / 479001600

private theorem endpoint_polynomial_nonneg {x : ℝ} (hx : 0 ≤ x) (h10 : x ≤ 10) :
    0 ≤ expPolynomial (9 * x / 40) - (1 - 9 / 20 + 9 / 20 * cosPolynomial x) := by
  have he : expPolynomial (9 * x / 40) - (1 - 9 / 20 + 9 / 20 * cosPolynomial x) =
      x ^ 2 * (
        21 / 32000000000 * (10 - x) ^ 7 +
        17 / 5120000000 * x * (10 - x) ^ 6 +
        101741 / 14336000000000 * x ^ 2 * (10 - x) ^ 5 +
        21109271 / 2580480000000000 * x ^ 3 * (10 - x) ^ 4 +
        3657844247 / 681246720000000000 * x ^ 4 * (10 - x) ^ 3 +
        1737950057 / 908328960000000000 * x ^ 5 * (10 - x) ^ 2 +
        8723361419 / 29066526720000000000 * x ^ 6 * (10 - x) +
        223958149 / 49828331520000000000 * x ^ 7) := by
    unfold expPolynomial cosPolynomial
    ring_nf
  rw [he]
  have hn : 0 ≤ 10 - x := sub_nonneg.mpr h10
  positivity

theorem bernoulli_endpoint_gaussian_sq_of_nonneg {t : ℝ} (ht : 0 ≤ t)
    (hpi : t ≤ Real.pi) :
    1 - 2 * (9 / 40 : ℝ) * (1 - Real.cos t) ≤ Real.exp (-(9 / 40 : ℝ) * t ^ 2) := by
  have hb : t ^ 2 ≤ 10 := by
    have hp := Real.pi_lt_d2
    nlinarith
  have hc : Real.cos t ≤ cosPolynomial (t ^ 2) := by
    have he := cos_le_taylor_twelve ht
    convert he using 1
    unfold cosPolynomial
    ring_nf
  have he : expPolynomial (9 * t ^ 2 / 40) ≤ Real.exp (-(9 / 40 : ℝ) * t ^ 2) := by
    have hp := exp_neg_ge_taylor_nine (x := 9 * t ^ 2 / 40) (by positivity)
    convert hp using 1
    congr 1
    ring_nf
  have hp := endpoint_polynomial_nonneg (sq_nonneg t) hb
  linarith

theorem bernoulli_endpoint_gaussian_sq {t : ℝ} (ht : |t| ≤ Real.pi) :
    1 - 2 * (9 / 40 : ℝ) * (1 - Real.cos t) ≤ Real.exp (-(9 / 40 : ℝ) * t ^ 2) := by
  simpa only [Real.cos_abs, sq_abs] using
    bernoulli_endpoint_gaussian_sq_of_nonneg (abs_nonneg t) ht

/-- Convexity of the exponential promotes a positive reference variance to
every larger variance. -/
theorem exp_variance_promotion {a v s c : ℝ} (ha : 0 < a) (hav : a ≤ v)
    (hbase : 1 - a * c ≤ Real.exp (-a * s)) :
    1 - v * c ≤ Real.exp (-v * s) := by
  have hv : 0 < v := ha.trans_le hav
  have hw : 0 ≤ 1 - a / v := sub_nonneg.mpr ((div_le_one hv).mpr hav)
  have he := convexOn_exp.2 (Set.mem_univ (-v * s)) (Set.mem_univ (0 : ℝ))
    (div_nonneg ha.le hv.le) hw (show a / v + (1 - a / v) = 1 by ring_nf)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at he
  have haeq : a / v * (-v * s) = -a * s := by field_simp
  rw [haeq] at he
  have hh := mul_le_mul_of_nonneg_left he hv.le
  have halg : v * (a / v * Real.exp (-v * s) + (1 - a / v)) =
      a * Real.exp (-v * s) + v - a := by field_simp; ring_nf
  rw [halg] at hh
  have hb := mul_le_mul_of_nonneg_left hbase hv.le
  apply (mul_le_mul_iff_of_pos_left ha).mp
  nlinarith

theorem bernoulli_variance_gaussian_sq {v t : ℝ} (hv : 9 / 40 ≤ v)
    (ht : |t| ≤ Real.pi) :
    1 - 2 * v * (1 - Real.cos t) ≤ Real.exp (-v * t ^ 2) := by
  have he := exp_variance_promotion (a := (9 / 40 : ℝ)) (v := v)
    (s := t ^ 2) (c := 2 * (1 - Real.cos t)) (by norm_num) hv
    (by nlinarith [bernoulli_endpoint_gaussian_sq ht])
  nlinarith

/-- The full-period near-symmetric Bernoulli bound from stage 500 §5.1.
All frequency and variance endpoints are included. -/
theorem centeredBernoulliCharacteristic_norm_le_gaussian {q t : ℝ}
    (hv : 9 / 40 ≤ q * (1 - q)) (ht : |t| ≤ Real.pi) :
    ‖centeredBernoulliCharacteristic q t‖ ≤
      Real.exp (-(q * (1 - q)) * t ^ 2 / 2) := by
  have he := bernoulli_variance_gaussian_sq hv ht
  rw [← centeredBernoulliCharacteristic_norm_sq] at he
  have hs : Real.exp (-(q * (1 - q)) * t ^ 2 / 2) ^ 2 =
      Real.exp (-(q * (1 - q)) * t ^ 2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring_nf
  rw [← hs] at he
  exact (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp he

theorem centeredBernoulliCharacteristic_pow_norm_le_gaussian (m : ℕ) {q t : ℝ}
    (hv : 9 / 40 ≤ q * (1 - q)) (ht : |t| ≤ Real.pi) :
    ‖centeredBernoulliCharacteristic q t ^ m‖ ≤
      Real.exp (-(m : ℝ) * (q * (1 - q)) * t ^ 2 / 2) := by
  rw [norm_pow]
  have he := pow_le_pow_left₀ (norm_nonneg _)
    (centeredBernoulliCharacteristic_norm_le_gaussian hv ht) m
  rw [← Real.exp_nat_mul] at he
  convert he using 1
  congr 1
  ring_nf

#print axioms centeredBernoulliCharacteristic_norm_sq
#print axioms cos_le_taylor_twelve
#print axioms exp_neg_ge_taylor_nine
#print axioms bernoulli_variance_gaussian_sq
#print axioms centeredBernoulliCharacteristic_norm_le_gaussian
#print axioms centeredBernoulliCharacteristic_pow_norm_le_gaussian
end ForestUnimodality
