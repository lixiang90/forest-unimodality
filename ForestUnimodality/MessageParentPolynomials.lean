import ForestUnimodality.MessageMarkedEnvelope

/-! Parent endpoint polynomials are calculated from the actual common
rational price segment. Both fixed points and the moving point 1-r are
instances of the same checked affine-coordinate identity. -/
namespace ForestUnimodality.MessagePriceSpline
open PolynomialList BernsteinCertificate

def affinePricePolynomial (lo hi left right a b : ℚ) : RatPolynomial :=
  C left+(C (a-lo)+C b*X)*C ((right-left)/(hi-lo))

theorem eval_affinePricePolynomial (lo hi left right a b : ℚ) (r : ℝ) :
    evalReal (affinePricePolynomial lo hi left right a b) r =
    (1-((a:ℝ)+(b:ℝ)*r-lo)/((hi:ℝ)-lo))*(left:ℝ)+
      (((a:ℝ)+(b:ℝ)*r-lo)/((hi:ℝ)-lo))*(right:ℝ) := by
  simp only [affinePricePolynomial,evalReal,eval_add,eval_mul,eval_C,eval_X]
  norm_num only [rationalEvaluation,Rat.cast_sub,Rat.cast_div]
  simp only [div_eq_mul_inv]
  ring

def Segment.parentPolynomials (c : Segment) (a b : ℚ) : MessagePolynomialEnvelope.ParentPrices :=
  ⟨affinePricePolynomial c.lo c.hi c.left.u c.right.u a b,
    affinePricePolynomial c.lo c.hi c.left.v c.right.v a b,
    affinePricePolynomial c.lo c.hi c.left.s c.right.s a b,
    affinePricePolynomial c.lo c.hi c.left.tau c.right.tau a b⟩

theorem Segment.parentPolynomials_eval (c : Segment) (a b : ℚ) (r : ℝ) :
    evalReal (c.parentPolynomials a b).u r=(c.atReal ((a:ℝ)+(b:ℝ)*r)).u ∧
    evalReal (c.parentPolynomials a b).v r=(c.atReal ((a:ℝ)+(b:ℝ)*r)).v ∧
    evalReal (c.parentPolynomials a b).s r=(c.atReal ((a:ℝ)+(b:ℝ)*r)).s ∧
    evalReal (c.parentPolynomials a b).tau r=(c.atReal ((a:ℝ)+(b:ℝ)*r)).tau := by
  simp only [Segment.parentPolynomials,Segment.atReal,eval_affinePricePolynomial,and_self]

theorem Segment.polynomial_envelope_eq_marked
    (c : Segment) (a b : ℚ) (r z : ℝ)
    (P : MessagePolynomialEnvelope.Parameters) (B : MessagePolynomialEnvelope.Bounds)
    (A : MessageSourceParameters)
    (hCJ : A.CJ=(P.CJ:ℝ)) (hCmu : A.Cmu=(P.Cmu:ℝ))
    (hw : A.w=(P.w:ℝ)) (ht : A.t=(P.t:ℝ)) :
    MessagePolynomialEnvelope.envelope P B (c.parentPolynomials a b) r z =
      messageSourceMarkedEnvelope A B.toReal r z
        (c.atReal ((a:ℝ)+(b:ℝ)*r)).u (c.atReal ((a:ℝ)+(b:ℝ)*r)).v
        (c.atReal ((a:ℝ)+(b:ℝ)*r)).s (c.atReal ((a:ℝ)+(b:ℝ)*r)).tau := by
  rw [MessagePolynomialEnvelope.envelope_eq_marked P B _ A r z hCJ hCmu hw ht]
  obtain ⟨hu,hv,hs,htau⟩ := c.parentPolynomials_eval a b r
  rw [hu,hv,hs,htau]

#print axioms Segment.parentPolynomials_eval
#print axioms Segment.polynomial_envelope_eq_marked
end ForestUnimodality.MessagePriceSpline
