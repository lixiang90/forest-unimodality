import ForestUnimodality.SourceSelectionCertificate
import ForestUnimodality.ParametricQuadratic

/-! Polynomial-in-retention certificates for the full unbounded real
response variable in a selection-source envelope. -/
namespace ForestUnimodality.SelectionSource
open PolynomialList BernsteinCertificate ParametricQuadratic

structure Parameters where
  CJ : ℚ
  Cmu : ℚ
  u : ℚ
  v : ℚ
  w : ℚ
  t : ℚ
  s : ℚ

noncomputable def Parameters.toReal (P : Parameters) : SelectionSourceParameters :=
  ⟨P.CJ,P.Cmu,P.u,P.v,P.w,P.t,P.s⟩

structure Bounds where
  L : ℚ
  H : ℚ
  hh : ℚ
  dd : ℚ
  phi : ℚ
  fs : ℚ
  fb : ℚ

noncomputable def envelope (P : Parameters) (d : Bounds) (r z : ℝ) : ℝ :=
  (P.CJ:ℝ)*r*((d.fs:ℝ)*r+d.fb)+(P.Cmu:ℝ)*r-r*d.dd*z^2+
  (P.u:ℝ)*((d.L:ℝ)*(max 0 (1-z))^2-d.hh*(max 0 z)^2)+
  (P.v:ℝ)*((d.L:ℝ)*(max 0 (z-1))^2-d.hh*(max 0 (-z))^2)+
  (P.w:ℝ)*(z-1+r*d.phi)+(P.t:ℝ)*(z-r)+
  (P.s:ℝ)*(r*(1-z)^2*d.H-(1-r)*d.dd*z^2)

def selectionPoly (P : Parameters) (d : Bounds) : RatPolynomial :=
  C (P.CJ*d.fs)*pow X 2+C (P.CJ*d.fb)*X

def negativeQuad (P : Parameters) (d : Bounds) : Quad where
  A := -X*C d.dd+C (P.u*d.L-P.v*d.hh)+C P.s*(X*C d.H-(1-X)*C d.dd)
  B := C (2*P.u*d.L-P.w-P.t)+C (2*P.s*d.H)*X
  C := selectionPoly P d+C P.Cmu*X+C (P.u*d.L-P.w)+C (P.w*d.phi-P.t+P.s*d.H)*X

def positiveQuad (P : Parameters) (d : Bounds) : Quad where
  A := -X*C d.dd+C (-P.u*d.hh+P.v*d.L)+C P.s*(X*C d.H-(1-X)*C d.dd)
  B := C (P.w+P.t-2*P.u*d.hh)-C (2*d.dd)*X-C (2*P.s*d.dd)*(1-X)
  C := selectionPoly P d+C (P.Cmu-d.dd+P.w*d.phi)*X-C (P.u*d.hh)+C (P.t-P.s*d.dd)*(1-X)

def middleQuad (P : Parameters) (d : Bounds) : Quad where
  A := -X*C d.dd+C (P.u*d.L-P.u*d.hh)+C P.s*(X*C d.H-(1-X)*C d.dd)
  B := -(positiveQuad P d).B
  C := (positiveQuad P d).C

theorem negativeQuad_identity (P : Parameters) (d : Bounds) (r x : ℝ) (hx : 0≤x) :
    envelope P d r (-x)=(negativeQuad P d).value r x := by
  have h1 : 0≤1+x := by linarith
  have h2 : -x-1≤0 := by linarith
  simp only [envelope,neg_neg,sub_neg_eq_add,max_eq_right h1,
    max_eq_left (neg_nonpos.mpr hx),max_eq_left h2,max_eq_right hx,
    negativeQuad,Quad.value,selectionPoly,evalReal,
    eval_add,eval_sub,eval_mul,eval_neg,eval_C,eval_X,eval_one,eval_pow]
  norm_num only [rationalEvaluation,Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_neg,Rat.cast_ofNat]
  ring

theorem positiveQuad_identity (P : Parameters) (d : Bounds) (r x : ℝ) (hx : 0≤x) :
    envelope P d r (1+x)=(positiveQuad P d).value r x := by
  have h1 : 0≤1+x := by linarith
  have h2 : 1-(1+x)= -x := by ring
  have h3 : 1+x-1=x := by ring
  simp only [envelope,h2,h3,max_eq_right h1,max_eq_left (neg_nonpos.mpr hx),
    max_eq_left (neg_nonpos.mpr h1),max_eq_right hx,
    positiveQuad,Quad.value,selectionPoly,evalReal,
    eval_add,eval_sub,eval_mul,eval_neg,eval_C,eval_X,eval_one,eval_pow]
  norm_num only [rationalEvaluation,Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_neg,Rat.cast_ofNat]
  ring

theorem middleQuad_identity (P : Parameters) (d : Bounds) (r x : ℝ)
    (hx : x∈Set.Icc (0:ℝ) 1) : envelope P d r (1-x)=(middleQuad P d).value r x := by
  have h1 : 1-(1-x)=x := by ring
  have h2 : 1-x-1= -x := by ring
  simp only [envelope,h1,h2,max_eq_left (neg_nonpos.mpr hx.1),
    max_eq_left (neg_nonpos.mpr (sub_nonneg.mpr hx.2)),max_eq_right hx.1,
    max_eq_right (sub_nonneg.mpr hx.2),middleQuad,positiveQuad,Quad.value,selectionPoly,evalReal,
    eval_add,eval_sub,eval_mul,eval_neg,eval_C,eval_X,eval_one,eval_pow]
  norm_num only [rationalEvaluation,Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_neg,Rat.cast_ofNat]
  ring

structure EnvelopeCertificate where
  lo : ℚ
  hi : ℚ
  negative : RayCertificate
  middle : UnitCertificate
  positive : RayCertificate

def EnvelopeCertificate.check (c : EnvelopeCertificate) (P : Parameters) (d : Bounds) : Bool :=
  c.negative.check (negativeQuad P d) c.lo c.hi &&
    c.middle.check (middleQuad P d) c.lo c.hi &&
    c.positive.check (positiveQuad P d) c.lo c.hi

theorem EnvelopeCertificate.check_sound {c : EnvelopeCertificate} {P : Parameters} {d : Bounds}
    (hc : c.check P d=true) {r z : ℝ} (hr : r∈Set.Icc (c.lo:ℝ) (c.hi:ℝ)) :
    0≤envelope P d r z := by
  have hs : c.negative.check (negativeQuad P d) c.lo c.hi=true ∧
      c.middle.check (middleQuad P d) c.lo c.hi=true ∧
      c.positive.check (positiveQuad P d) c.lo c.hi=true := by
    simpa only [EnvelopeCertificate.check,Bool.and_eq_true_iff,and_assoc] using hc
  by_cases hz : z≤0
  · have h := c.negative.check_sound hs.1 hr (neg_nonneg.mpr hz)
    rw [←negativeQuad_identity P d r (-z) (neg_nonneg.mpr hz),neg_neg] at h
    exact h
  · have hz0 : 0≤z := (lt_of_not_ge hz).le
    by_cases hz1 : z≤1
    · have hx : 1-z∈Set.Icc (0:ℝ) 1 := ⟨sub_nonneg.mpr hz1,by linarith⟩
      have h := c.middle.check_sound hs.2.1 hr hx
      rw [←middleQuad_identity P d r (1-z) hx] at h
      convert h using 1
      congr 1
      ring
    · have hx : 0≤z-1 := by linarith
      have h := c.positive.check_sound hs.2.2 hr hx
      rw [←positiveQuad_identity P d r (z-1) hx] at h
      convert h using 1
      congr 1
      ring

#print axioms negativeQuad_identity
#print axioms positiveQuad_identity
#print axioms middleQuad_identity
#print axioms EnvelopeCertificate.check_sound
end ForestUnimodality.SelectionSource
