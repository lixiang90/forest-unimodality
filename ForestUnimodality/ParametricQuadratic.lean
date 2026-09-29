import ForestUnimodality.BernsteinCertificate
import ForestUnimodality.QuadraticCertificate

/-! Quadratic response certificates whose coefficients are rational
polynomials in a second, continuously varying parameter. -/
namespace ForestUnimodality.ParametricQuadratic
open PolynomialList BernsteinCertificate

structure Quad where
  A : RatPolynomial
  B : RatPolynomial
  C : RatPolynomial

noncomputable def Quad.value (Q : Quad) (r x : ℝ) : ℝ :=
  evalReal Q.A r*x^2+evalReal Q.B r*x+evalReal Q.C r

def Quad.discriminantMargin (Q : Quad) : RatPolynomial :=
  PolynomialList.C 4*Q.A*Q.C-pow Q.B 2

structure RayCertificate where
  leading : Certificate
  endpoint : Certificate
  useSlope : Bool
  last : Certificate

def RayCertificate.check (c : RayCertificate) (Q : Quad) (lo hi : ℚ) : Bool :=
  intervalCheck Q.A lo hi c.leading && intervalCheck Q.C lo hi c.endpoint &&
    intervalCheck (if c.useSlope then Q.B else Q.discriminantMargin) lo hi c.last

theorem eval_discriminantMargin (Q : Quad) (r : ℝ) :
    evalReal Q.discriminantMargin r=4*evalReal Q.A r*evalReal Q.C r-(evalReal Q.B r)^2 := by
  simp only [Quad.discriminantMargin,evalReal,eval_sub,eval_mul,eval_C,eval_pow]
  norm_num [rationalEvaluation]

theorem RayCertificate.check_sound {c : RayCertificate} {Q : Quad} {lo hi : ℚ}
    (hc : c.check Q lo hi=true) {r x : ℝ} (hr : r∈Set.Icc (lo:ℝ) (hi:ℝ))
    (hx : 0≤x) : 0≤Q.value r x := by
  have hs : intervalCheck Q.A lo hi c.leading=true ∧ intervalCheck Q.C lo hi c.endpoint=true ∧
      intervalCheck (if c.useSlope then Q.B else Q.discriminantMargin) lo hi c.last=true := by
    simpa only [RayCertificate.check,Bool.and_eq_true_iff,and_assoc] using hc
  have ha := intervalCheck_sound hs.1 hr
  have hC := intervalCheck_sound hs.2.1 hr
  have he := intervalCheck_sound hs.2.2 hr
  apply QuadraticCertificate.quadratic_nonneg_on_nonneg ha hC ?_ hx
  cases hb : c.useSlope
  · simp only [hb,Bool.false_eq_true,if_false,eval_discriminantMargin] at he
    exact Or.inr (by linarith)
  · simp only [hb,if_true] at he
    exact Or.inl he

inductive UnitBranch where
  | concave
  | increasing
  | decreasing
  | discriminant
  deriving DecidableEq, Repr

structure UnitCertificate where
  left : Certificate
  right : Certificate
  branch : UnitBranch
  last : Certificate

def UnitBranch.polynomial (b : UnitBranch) (Q : Quad) : RatPolynomial :=
  match b with
  | .concave => -Q.A
  | .increasing => Q.B
  | .decreasing => -(PolynomialList.C 2*Q.A)-Q.B
  | .discriminant => Q.discriminantMargin

def UnitCertificate.check (c : UnitCertificate) (Q : Quad) (lo hi : ℚ) : Bool :=
  intervalCheck Q.C lo hi c.left && intervalCheck (Q.A+Q.B+Q.C) lo hi c.right &&
    intervalCheck (c.branch.polynomial Q) lo hi c.last

/-- Complete real interval criterion, including concavity and both endpoint
minima as well as an interior vertex. -/
theorem quadratic_nonneg_on_unit {a b c x : ℝ}
    (hc : 0≤c) (h1 : 0≤a+b+c)
    (hb : a≤0 ∨ 0≤b ∨ b≤-2*a ∨ b^2≤4*a*c)
    (hx : x∈Set.Icc (0:ℝ) 1) : 0≤a*x^2+b*x+c := by
  rcases hb with ha | hb | hb | hd
  · nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2),
      mul_nonneg (neg_nonneg.mpr ha) (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)),
      mul_nonneg hx.1 h1,mul_nonneg (sub_nonneg.mpr hx.2) hc]
  · by_cases ha : 0≤a
    · exact add_nonneg (add_nonneg (mul_nonneg ha (sq_nonneg x)) (mul_nonneg hb hx.1)) hc
    · have hh : a≤0 := le_of_not_ge ha
      nlinarith [mul_nonneg (neg_nonneg.mpr hh) (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)),
        mul_nonneg hx.1 h1,mul_nonneg (sub_nonneg.mpr hx.2) hc]
  · by_cases ha : 0≤a
    · have hdiff : 0≤(1-x)*(-a*(1+x)-b) := by
        apply mul_nonneg (sub_nonneg.mpr hx.2)
        nlinarith [mul_le_mul_of_nonneg_left hx.2 ha]
      nlinarith
    · have hh : a≤0 := le_of_not_ge ha
      nlinarith [mul_nonneg (neg_nonneg.mpr hh) (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)),
        mul_nonneg hx.1 h1,mul_nonneg (sub_nonneg.mpr hx.2) hc]
  · by_cases ha : 0≤a
    · exact QuadraticCertificate.quadratic_nonneg_on_nonneg ha hc (Or.inr hd) hx.1
    · have hh : a≤0 := le_of_not_ge ha
      nlinarith [mul_nonneg (neg_nonneg.mpr hh) (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)),
        mul_nonneg hx.1 h1,mul_nonneg (sub_nonneg.mpr hx.2) hc]

theorem UnitCertificate.check_sound {c : UnitCertificate} {Q : Quad} {lo hi : ℚ}
    (hc : c.check Q lo hi=true) {r x : ℝ} (hr : r∈Set.Icc (lo:ℝ) (hi:ℝ))
    (hx : x∈Set.Icc (0:ℝ) 1) : 0≤Q.value r x := by
  have hs : intervalCheck Q.C lo hi c.left=true ∧ intervalCheck (Q.A+Q.B+Q.C) lo hi c.right=true ∧
      intervalCheck (c.branch.polynomial Q) lo hi c.last=true := by
    simpa only [UnitCertificate.check,Bool.and_eq_true_iff,and_assoc] using hc
  have hC := intervalCheck_sound hs.1 hr
  have h1 := intervalCheck_sound hs.2.1 hr
  have he := intervalCheck_sound hs.2.2 hr
  simp only [evalReal,eval_add] at h1
  change 0≤evalReal Q.A r+evalReal Q.B r+evalReal Q.C r at h1
  apply quadratic_nonneg_on_unit hC h1 ?_ hx
  cases hb : c.branch
  · simp only [hb,UnitBranch.polynomial,evalReal,eval_neg] at he
    change 0≤-evalReal Q.A r at he
    exact Or.inl (by linarith)
  · simp only [hb,UnitBranch.polynomial] at he
    exact Or.inr (Or.inl he)
  · simp only [hb,UnitBranch.polynomial,evalReal,eval_sub,eval_neg,eval_mul,eval_C] at he
    norm_num only [rationalEvaluation] at he
    change 0≤-(2*evalReal Q.A r)-evalReal Q.B r at he
    exact Or.inr (Or.inr (Or.inl (by linarith)))
  · simp only [hb,UnitBranch.polynomial,eval_discriminantMargin] at he
    exact Or.inr (Or.inr (Or.inr (by linarith)))

#print axioms RayCertificate.check_sound
#print axioms UnitCertificate.check_sound
end ForestUnimodality.ParametricQuadratic
