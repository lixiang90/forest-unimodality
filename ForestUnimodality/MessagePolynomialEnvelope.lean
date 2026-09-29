import ForestUnimodality.MessageSourceEnvelope
import ForestUnimodality.ParametricQuadratic

/-! Exact rational response polynomials for stage80 message-price envelopes.
Parent prices may be polynomials in the same retention variable, covering
both fixed knot points and the moving endpoint parentp=1-r. -/
namespace ForestUnimodality.MessagePolynomialEnvelope
open PolynomialList BernsteinCertificate ParametricQuadratic

structure Parameters where
  CJ : ℚ
  Cmu : ℚ
  w : ℚ
  t : ℚ

structure Bounds where
  L : ℚ
  H : ℚ
  hh : ℚ
  dd : ℚ
  phi : ℚ
  fs : ℚ
  fb : ℚ
  logLower : ℚ
  u : ℚ
  v : ℚ
  s : ℚ
  tau : ℚ

structure ParentPrices where
  u : RatPolynomial
  v : RatPolynomial
  s : RatPolynomial
  tau : RatPolynomial

noncomputable def Bounds.toReal (B : Bounds) : MessageEnvelopeBounds :=
  ⟨B.L,B.H,B.hh,B.dd,B.phi,B.fs,B.fb,B.logLower,B.u,B.v,B.s,B.tau⟩

noncomputable def envelope (P : Parameters) (B : Bounds) (Q : ParentPrices) (r z : ℝ) : ℝ :=
  (P.CJ:ℝ)*r*((B.fs:ℝ)*r+B.fb)+(P.Cmu:ℝ)*r-r*B.dd*z^2+
  (B.u:ℝ)*B.L*(max 0 (1-z))^2-evalReal Q.u r*B.hh*(max 0 z)^2+
  (B.v:ℝ)*B.L*(max 0 (z-1))^2-evalReal Q.v r*B.hh*(max 0 (-z))^2+
  (B.s:ℝ)*r*(1-z)^2*B.H-(1-r)*evalReal Q.s r*B.dd*z^2+
  (P.w:ℝ)*(z-1+r*B.phi)+(P.t:ℝ)*(z-r)+
  r*B.tau*(z-1)+(1-r)*evalReal Q.tau r*z+B.logLower

theorem envelope_eq_actual (P : Parameters) (B : Bounds) (Q : ParentPrices)
    (A : MessageSourceParameters) (r z parentp : ℝ)
    (hCJ : A.CJ=(P.CJ:ℝ)) (hCmu : A.Cmu=(P.Cmu:ℝ))
    (hw : A.w=(P.w:ℝ)) (ht : A.t=(P.t:ℝ))
    (hu : A.u parentp=evalReal Q.u r) (hv : A.v parentp=evalReal Q.v r)
    (hs : A.s parentp=evalReal Q.s r) (htau : A.tau parentp=evalReal Q.tau r) :
    envelope P B Q r z=messageSourceEnvelope A B.toReal r z parentp := by
  simp only [envelope,messageSourceEnvelope,Bounds.toReal,hCJ,hCmu,hw,ht,hu,hv,hs,htau]

def selectionPoly (P : Parameters) (B : Bounds) : RatPolynomial :=
  C (P.CJ*B.fs)*pow X 2+C (P.CJ*B.fb)*X

def negativeQuad (P : Parameters) (B : Bounds) (Q : ParentPrices) : Quad where
  A := -X*C B.dd+C (B.u*B.L)-Q.v*C B.hh+C (B.s*B.H)*X-(1-X)*Q.s*C B.dd
  B := C (2*B.u*B.L-P.w-P.t)+C (2*B.s*B.H-B.tau)*X-(1-X)*Q.tau
  C := selectionPoly P B+C (P.Cmu+P.w*B.phi-P.t+B.s*B.H-B.tau)*X+
    C (B.u*B.L-P.w+B.logLower)

def middleQuad (P : Parameters) (B : Bounds) (Q : ParentPrices) : Quad where
  A := -X*C B.dd+C (B.u*B.L)-Q.u*C B.hh+C (B.s*B.H)*X-(1-X)*Q.s*C B.dd
  B := C (-2*B.u*B.L+P.w+P.t)+C (-2*B.s*B.H+B.tau)*X+(1-X)*Q.tau
  C := (negativeQuad P B Q).C

def positiveQuad (P : Parameters) (B : Bounds) (Q : ParentPrices) : Quad where
  A := -X*C B.dd-Q.u*C B.hh+C (B.v*B.L)+C (B.s*B.H)*X-(1-X)*Q.s*C B.dd
  B := -C (2*B.dd)*X-C (2*B.hh)*Q.u-C (2*B.dd)*(1-X)*Q.s+
    C (P.w+P.t)+C B.tau*X+(1-X)*Q.tau
  C := selectionPoly P B+C (P.Cmu-B.dd+P.w*B.phi)*X-Q.u*C B.hh-
    (1-X)*Q.s*C B.dd+C P.t*(1-X)+(1-X)*Q.tau+C B.logLower

theorem negativeQuad_identity (P : Parameters) (B : Bounds) (Q : ParentPrices)
    (r x : ℝ) (hx : 0≤x) : envelope P B Q r (-x)=(negativeQuad P B Q).value r x := by
  have h1 : 0≤1+x := by linarith
  have h2 : -x-1≤0 := by linarith
  simp only [envelope,neg_neg,sub_neg_eq_add,max_eq_right h1,
    max_eq_left (neg_nonpos.mpr hx),max_eq_left h2,max_eq_right hx,
    negativeQuad,Quad.value,selectionPoly,evalReal,
    eval_add,eval_sub,eval_mul,eval_neg,eval_C,eval_X,eval_one,eval_pow]
  norm_num only [rationalEvaluation,Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_neg,Rat.cast_ofNat]
  ring

theorem middleQuad_identity (P : Parameters) (B : Bounds) (Q : ParentPrices)
    (r x : ℝ) (hx : x∈Set.Icc (0:ℝ) 1) : envelope P B Q r x=(middleQuad P B Q).value r x := by
  have h1 := sub_nonneg.mpr hx.2
  have h2 : x-1≤0 := by linarith [hx.2]
  simp only [envelope,max_eq_right h1,max_eq_right hx.1,max_eq_left h2,
    max_eq_left (neg_nonpos.mpr hx.1),middleQuad,negativeQuad,Quad.value,selectionPoly,evalReal,
    eval_add,eval_sub,eval_mul,eval_neg,eval_C,eval_X,eval_one,eval_pow]
  norm_num only [rationalEvaluation,Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_neg,Rat.cast_ofNat]
  ring

theorem positiveQuad_identity (P : Parameters) (B : Bounds) (Q : ParentPrices)
    (r x : ℝ) (hx : 0≤x) : envelope P B Q r (1+x)=(positiveQuad P B Q).value r x := by
  have h1 : 0≤1+x := by linarith
  have h2 : 1-(1+x)= -x := by ring
  have h3 : 1+x-1=x := by ring
  simp only [envelope,h2,h3,max_eq_right h1,max_eq_left (neg_nonpos.mpr hx),
    max_eq_left (neg_nonpos.mpr h1),max_eq_right hx,
    positiveQuad,Quad.value,selectionPoly,evalReal,
    eval_add,eval_sub,eval_mul,eval_neg,eval_C,eval_X,eval_one,eval_pow]
  norm_num only [rationalEvaluation,Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_neg,Rat.cast_ofNat]
  ring

theorem negative_check_sound {P : Parameters} {B : Bounds} {Q : ParentPrices}
    {c : RayCertificate} {lo hi : ℚ} (hc : c.check (negativeQuad P B Q) lo hi=true)
    {r z : ℝ} (hr : r∈Set.Icc (lo:ℝ) (hi:ℝ)) (hz : z≤0) : 0≤envelope P B Q r z := by
  have hh := c.check_sound hc hr (neg_nonneg.mpr hz)
  rwa [←negativeQuad_identity P B Q r (-z) (neg_nonneg.mpr hz),neg_neg] at hh

theorem middle_check_sound {P : Parameters} {B : Bounds} {Q : ParentPrices}
    {c : UnitCertificate} {lo hi : ℚ} (hc : c.check (middleQuad P B Q) lo hi=true)
    {r z : ℝ} (hr : r∈Set.Icc (lo:ℝ) (hi:ℝ)) (hz : z∈Set.Icc (0:ℝ) 1) :
    0≤envelope P B Q r z := by
  rw [middleQuad_identity P B Q r z hz]
  exact c.check_sound hc hr hz

theorem positive_check_sound {P : Parameters} {B : Bounds} {Q : ParentPrices}
    {c : RayCertificate} {lo hi : ℚ} (hc : c.check (positiveQuad P B Q) lo hi=true)
    {r z : ℝ} (hr : r∈Set.Icc (lo:ℝ) (hi:ℝ)) (hz : 1≤z) : 0≤envelope P B Q r z := by
  have hx : 0≤z-1 := sub_nonneg.mpr hz
  have hh := c.check_sound hc hr hx
  rw [←positiveQuad_identity P B Q r (z-1) hx] at hh
  simpa only [add_sub_cancel] using hh

#print axioms negative_check_sound
#print axioms middle_check_sound
#print axioms positive_check_sound
end ForestUnimodality.MessagePolynomialEnvelope
