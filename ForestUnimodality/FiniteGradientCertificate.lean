import ForestUnimodality.BinomialGradientConstants
import ForestUnimodality.BernsteinCertificate

/-! Univariate certificates for the actual low-order weighted binomial gradient.
The target polynomial is rebuilt from n, j, and the sign; it is not witness data. -/
namespace ForestUnimodality.FiniteGradientCertificate
open PolynomialList BernsteinCertificate

def massPolynomial (n j : ℕ) : RatPolynomial :=
  C (n.choose j : ℚ) * pow X j * pow (1 - X) (n - j)

def targetPolynomial (n j : ℕ) (positive : Bool) : RatPolynomial :=
  C (31 / 100) + C (if positive then 1 else -1) * (C (n : ℚ) * X - C (j : ℚ)) *
    massPolynomial n j

theorem eval_massPolynomial (n j : ℕ) (q : ℝ) :
    evalReal (massPolynomial n j) q = binomialMass n j q := by
  rw [binomialMass_nat]
  simp only [evalReal, massPolynomial, eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one]
  simp [rationalEvaluation]

theorem eval_targetPolynomial (n j : ℕ) (positive : Bool) (q : ℝ) :
    evalReal (targetPolynomial n j positive) q =
      31 / 100 + (if positive then (1 : ℝ) else -1) * ((n : ℝ) * q - j) * binomialMass n j q := by
  simp only [targetPolynomial, evalReal, eval_add, eval_mul, eval_C, eval_X, eval_sub]
  rw [show eval rationalEvaluation.value q (massPolynomial n j) = binomialMass n j q from
    eval_massPolynomial n j q]
  cases positive <;> simp [rationalEvaluation]

inductive Cover where
  | leaf (certificate : Certificate)
  | split (left right : Cover)

def Cover.check (p : RatPolynomial) (lo hi : ℚ) : Cover → Bool
  | .leaf c => intervalCheck p lo hi c
  | .split l r => l.check p lo ((lo + hi) / 2) && r.check p ((lo + hi) / 2) hi

theorem Cover.check_sound (tree : Cover) {p : RatPolynomial} {lo hi : ℚ}
    (hc : tree.check p lo hi = true) {q : ℝ}
    (hq : q ∈ Set.Icc (lo : ℝ) (hi : ℝ)) : 0 ≤ evalReal p q := by
  induction tree generalizing lo hi with
  | leaf c => exact intervalCheck_sound hc hq
  | split l r ihl ihr =>
    have hs : l.check p lo ((lo + hi) / 2) = true ∧ r.check p ((lo + hi) / 2) hi = true := by
      simpa only [Cover.check, Bool.and_eq_true_iff] using hc
    by_cases hm : q ≤ (((lo + hi) / 2 : ℚ) : ℝ)
    · exact ihl hs.1 ⟨hq.1, hm⟩
    · exact ihr hs.2 ⟨(lt_of_not_ge hm).le, hq.2⟩

theorem weightedDeviation_le_of_checks (n j : ℕ) (positive negative : Cover)
    (hp : positive.check (targetPolynomial n j true) (3 / 10) (7 / 10) = true)
    (hn : negative.check (targetPolynomial n j false) (3 / 10) (7 / 10) = true)
    {q : ℝ} (hq : q ∈ Set.Icc (3 / 10 : ℝ) (7 / 10)) :
    |(n : ℝ) * q - j| * binomialMass n j q ≤ 31 / 100 := by
  have hq' : q ∈ Set.Icc (((3 / 10 : ℚ) : ℝ)) (((7 / 10 : ℚ) : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hq
  have hp' := positive.check_sound hp hq'
  have hn' := negative.check_sound hn hq'
  rw [eval_targetPolynomial] at hp' hn'
  simp only [ite_true, one_mul, Bool.false_eq_true, ite_false, neg_one_mul] at hp' hn'
  have hb := binomialMass_nonneg n j (q := q) (by linarith [hq.1]) (by linarith [hq.2])
  rw [← abs_of_nonneg hb, ← abs_mul]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

#print axioms eval_targetPolynomial
#print axioms Cover.check_sound
#print axioms weightedDeviation_le_of_checks
end ForestUnimodality.FiniteGradientCertificate
