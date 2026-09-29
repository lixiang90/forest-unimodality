import ForestUnimodality.BernsteinCover
import Mathlib.Tactic

/-! Exact homogeneous compactification of sparse bivariate polynomials.
Both the numerator identity and the positive denominator are retained. -/
namespace ForestUnimodality.RationalCompactification

open PolynomialList BernsteinCertificate

theorem evalReal₂_eq_of_equalCheck {p q : BiPolynomial}
    (h : equalCheck (zeroCheck ratZero) p q = true) (x y : ℝ) :
    evalReal₂ p x y = evalReal₂ q x y := by
  have hz : ∀ a, zeroCheck ratZero a = true → (liftEvaluation rationalEvaluation x).value a = 0 := by
    intro a ha
    exact zeroCheck_sound rationalEvaluation.value ratZero ratZero_sound ha x
  exact equalCheck_sound (liftEvaluation rationalEvaluation x) _ hz h y

structure Term where
  degreeX : ℕ
  degreeY : ℕ
  coeff : ℚ
  deriving DecidableEq, Repr

noncomputable def evalSparse (terms : List Term) (x y : ℝ) : ℝ :=
  (terms.map fun t => (t.coeff : ℝ) * x ^ t.degreeX * y ^ t.degreeY).sum

def degreeCheck (terms : List Term) (dx dy : ℕ) : Bool :=
  terms.all (fun t => decide (t.degreeX ≤ dx ∧ t.degreeY ≤ dy))

def compactPolynomial (terms : List Term) (dx dy : ℕ) (second : Bool) : BiPolynomial :=
  let u : BiPolynomial := C X
  let v : BiPolynomial := X
  let d : BiPolynomial := if second then 1 - v else 1
  sum (terms.map fun t => C (C t.coeff) * pow u t.degreeX * pow (1 - u) (dx - t.degreeX) *
    pow v t.degreeY * pow d (dy - t.degreeY))

theorem eval_compactPolynomial (terms : List Term) (dx dy : ℕ) (second : Bool) (u v : ℝ) :
    evalReal₂ (compactPolynomial terms dx dy second) u v =
      (terms.map fun t => (t.coeff : ℝ) * u ^ t.degreeX * (1 - u) ^ (dx - t.degreeX) *
        v ^ t.degreeY * (if second then 1 - v else 1) ^ (dy - t.degreeY)).sum := by
  unfold compactPolynomial evalReal₂
  rw [eval_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  cases second <;>
    simp only [Function.comp_apply, Bool.false_eq_true, ↓reduceIte,
      eval_mul, eval_pow, eval_sub, eval_one, eval_X, eval_C]
  all_goals
    change eval rationalEvaluation.value u (C t.coeff) *
      eval rationalEvaluation.value u X ^ t.degreeX *
      (1 - eval rationalEvaluation.value u X) ^ (dx - t.degreeX) * v ^ t.degreeY * _ = _
    simp only [eval_C, eval_X]
    rfl

theorem homogeneous_power {i d : ℕ} (hi : i ≤ d) (a b : ℝ) (hb : b ≠ 0) :
    a ^ i * b ^ (d - i) = b ^ d * (a / b) ^ i := by
  rw [div_pow, ← mul_div_assoc, eq_div_iff (pow_ne_zero _ hb)]
  calc
    a ^ i * b ^ (d - i) * b ^ i = a ^ i * b ^ ((d - i) + i) := by rw [pow_add]; ring
    _ = b ^ d * a ^ i := by rw [Nat.sub_add_cancel hi]; ring

theorem compact_identity (terms : List Term) (dx dy : ℕ) (second : Bool)
    (hdegree : degreeCheck terms dx dy = true) (u v : ℝ)
    (hu : 1 - u ≠ 0) (hv : (if second then 1 - v else 1 : ℝ) ≠ 0) :
    evalReal₂ (compactPolynomial terms dx dy second) u v =
      (1 - u) ^ dx * (if second then 1 - v else 1 : ℝ) ^ dy *
        evalSparse terms (u / (1 - u)) (v / (if second then 1 - v else 1)) := by
  rw [eval_compactPolynomial]
  unfold evalSparse
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro t ht
  have hdegrees : t.degreeX ≤ dx ∧ t.degreeY ≤ dy :=
    of_decide_eq_true (List.all_eq_true.mp hdegree t ht)
  have hx := homogeneous_power hdegrees.1 u (1 - u) hu
  have hy := homogeneous_power hdegrees.2 v (if second then 1 - v else 1) hv
  calc
    _ = (t.coeff : ℝ) * (u ^ t.degreeX * (1 - u) ^ (dx - t.degreeX)) *
        (v ^ t.degreeY * (if second then 1 - v else 1) ^ (dy - t.degreeY)) := by ring
    _ = _ := by rw [hx, hy]; ring

theorem compact_parameter {x : ℝ} (hx : 0 ≤ x) :
    x / (1 + x) ∈ Set.Icc (0 : ℝ) 1 ∧ 0 < 1 - x / (1 + x) ∧
      (x / (1 + x)) / (1 - x / (1 + x)) = x := by
  have hp : 0 < 1 + x := by positivity
  have he : 1 - x / (1 + x) = 1 / (1 + x) := by field_simp; ring
  refine ⟨⟨div_nonneg hx hp.le, (div_le_one hp).mpr (by linarith)⟩, ?_, ?_⟩
  · rw [he]; positivity
  · rw [he]; field_simp

theorem nonneg_of_compact (terms : List Term) (dx dy : ℕ) (second : Bool)
    (hdegree : degreeCheck terms dx dy = true)
    (hcompact : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ evalReal₂ (compactPolynomial terms dx dy second) u v)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hy1 : second = false → y ≤ 1) :
    0 ≤ evalSparse terms x y := by
  obtain ⟨hux, hud, hueq⟩ := compact_parameter hx
  cases second with
  | false =>
    have hc := hcompact _ hux y ⟨hy, hy1 rfl⟩
    rw [compact_identity terms dx dy false hdegree _ _ hud.ne' (by norm_num)] at hc
    simp only [Bool.false_eq_true, ↓reduceIte, one_pow, mul_one, div_one, hueq] at hc
    exact nonneg_of_mul_nonneg_right hc (pow_pos hud _)
  | true =>
    obtain ⟨hvy, hvd, hveq⟩ := compact_parameter hy
    have hc := hcompact _ hux _ hvy
    rw [compact_identity terms dx dy true hdegree _ _ hud.ne' hvd.ne'] at hc
    simp only [↓reduceIte, hueq, hveq] at hc
    exact nonneg_of_mul_nonneg_right hc (mul_pos (pow_pos hud _) (pow_pos hvd _))

#print axioms compact_identity
#print axioms nonneg_of_compact
end ForestUnimodality.RationalCompactification
