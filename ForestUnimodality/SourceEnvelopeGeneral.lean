import ForestUnimodality.SourceEnvelopeCertificate
import ForestUnimodality.SourceParameters

/-! Rational quadratic certificates for an entire response/retention
envelope. The transcendental source-to-envelope bound is checked separately. -/
namespace ForestUnimodality.ParametricSourceEnvelope
variable (P : RationalSourceParameters)

structure Bounds where
  L : ℚ
  H : ℚ
  hh : ℚ
  dd : ℚ
  B : ℚ
  phi : ℚ
  rl : ℚ
  rh : ℚ

noncomputable def envelope (L H hh dd B phi a parentA r z : ℝ) : ℝ :=
  let R := P.toReal
  r*(R.A+R.C*a)-r*dd*z^2+B +
    R.positivePrice a*L*(max 0 (a-z))^2-R.positivePrice parentA*hh*(max 0 z)^2 +
    R.negativePrice a*L*(max 0 (z-a))^2-R.negativePrice parentA*hh*(max 0 (-z))^2 +
    R.responsePrice*(z-r*a)+R.blockingPrice*(r*(a-z)^2*H-(1-r)*dd*z^2) + R.phiPrice*(r*(1+phi)-1)

namespace Checker
open SourceEnvelopeCertificate (Quad)
def posPrice (a : ℚ) : ℚ := if a=1 then P.u1 else P.u0
def negPrice (a : ℚ) : ℚ := if a=1 then P.v1 else P.v0

theorem posPrice_cast (a : ℚ) : (posPrice P a : ℝ) = P.toReal.positivePrice a := by
  by_cases h : a=1
  · simp [posPrice, h, RationalSourceParameters.toReal]
  · have hr : (a : ℝ) ≠ 1 := by exact_mod_cast h
    simp [posPrice, h, RationalSourceParameters.toReal, hr]

theorem negPrice_cast (a : ℚ) : (negPrice P a : ℝ) = P.toReal.negativePrice a := by
  by_cases h : a=1
  · simp [negPrice, h, RationalSourceParameters.toReal]
  · have hr : (a : ℝ) ≠ 1 := by exact_mod_cast h
    simp [negPrice, h, RationalSourceParameters.toReal, hr]

def negativeQuad (d : Bounds) (a pa r : ℚ) : Quad where
  A := -r*d.dd+posPrice P a*d.L-negPrice P pa*d.hh+
    (P.s)*(r*d.H-(1-r)*d.dd)
  B := 2*a*posPrice P a*d.L-P.t+2*a*(P.s)*r*d.H
  C := r*(P.A+(P.C)*a)+d.B+P.w*(r*(1+d.phi)-1)-
    (P.t)*r*a+posPrice P a*d.L*a^2+(P.s)*r*d.H*a^2

def positiveQuad (d : Bounds) (a pa r : ℚ) : Quad where
  A := -r*d.dd-posPrice P pa*d.hh+negPrice P a*d.L+
    (P.s)*(r*d.H-(1-r)*d.dd)
  B := -2*a*r*d.dd-2*a*posPrice P pa*d.hh+P.t-
    2*a*(P.s)*(1-r)*d.dd
  C := r*(P.A+(P.C)*a)+d.B+P.w*(r*(1+d.phi)-1)+
    (P.t)*(a-r*a)-a^2*r*d.dd-posPrice P pa*d.hh*a^2-
    (P.s)*(1-r)*d.dd*a^2

def middleQuad (d : Bounds) (r : ℚ) : Quad where
  A := -r*d.dd+posPrice P 1*d.L-posPrice P 0*d.hh+
    (P.s)*(r*d.H-(1-r)*d.dd)
  B := 2*r*d.dd+2*posPrice P 0*d.hh-P.t+
    2*(P.s)*(1-r)*d.dd
  C := (positiveQuad P d 1 0 r).C

theorem negativeQuad_identity (d : Bounds) (a pa r : ℚ) (x : ℝ)
    (ha : 0 ≤ a) (hx : 0 ≤ x) :
    envelope P d.L d.H d.hh d.dd d.B d.phi a pa r (-x) =
      ((negativeQuad P d a pa r).A : ℝ)*x^2+((negativeQuad P d a pa r).B : ℝ)*x+
        (negativeQuad P d a pa r).C := by
  have har : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hap : 0 ≤ (a : ℝ)+x := by linarith
  have han : -x-(a : ℝ) ≤ 0 := by linarith
  simp only [envelope, neg_neg, sub_neg_eq_add, max_eq_right hap,
    max_eq_left (neg_nonpos.mpr hx), max_eq_left han, max_eq_right hx,
    negativeQuad]
  push_cast
  rw [posPrice_cast, negPrice_cast]
  simp only [RationalSourceParameters.toReal]
  ring

theorem positiveQuad_identity (d : Bounds) (a pa r : ℚ) (x : ℝ)
    (ha : 0 ≤ a) (hx : 0 ≤ x) :
    envelope P d.L d.H d.hh d.dd d.B d.phi a pa r ((a : ℝ)+x) =
      ((positiveQuad P d a pa r).A : ℝ)*x^2+((positiveQuad P d a pa r).B : ℝ)*x+
        (positiveQuad P d a pa r).C := by
  have har : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hap : 0 ≤ (a : ℝ)+x := by linarith
  have ha1 : (a : ℝ)-((a : ℝ)+x) = -x := by ring
  have ha2 : (a : ℝ)+x-(a : ℝ) = x := by ring
  simp only [envelope, ha1, ha2, max_eq_left (neg_nonpos.mpr hx),
    max_eq_left (neg_nonpos.mpr hap), max_eq_right hx, max_eq_right hap, positiveQuad]
  push_cast
  rw [posPrice_cast, negPrice_cast]
  simp only [RationalSourceParameters.toReal]
  ring

theorem middleQuad_identity (d : Bounds) (r : ℚ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    envelope P d.L d.H d.hh d.dd d.B d.phi 1 0 r (1-x) =
      ((middleQuad P d r).A : ℝ)*x^2+((middleQuad P d r).B : ℝ)*x+(middleQuad P d r).C := by
  have h1 : 1-(1-x)=x := by ring
  have h2 : 1-x-1= -x := by ring
  simp only [envelope, h1, h2, max_eq_left (neg_nonpos.mpr hx.1),
    max_eq_left (neg_nonpos.mpr (sub_nonneg.mpr hx.2)), max_eq_right hx.1,
    max_eq_right (sub_nonneg.mpr hx.2), middleQuad, positiveQuad]
  norm_num [posPrice, negPrice, RationalSourceParameters.toReal]
  ring

def endpointCheck (d : Bounds) (r : ℚ) : Bool :=
  (negativeQuad P d 0 0 r).rayCheck && (positiveQuad P d 0 0 r).rayCheck &&
  (negativeQuad P d 0 1 r).rayCheck && (positiveQuad P d 0 1 r).rayCheck &&
  (negativeQuad P d 1 0 r).rayCheck && (positiveQuad P d 1 0 r).rayCheck && (middleQuad P d r).unitCheck

theorem endpointCheck_sound {d : Bounds} {r : ℚ} (h : endpointCheck P d r=true)
    {a pa : ℝ} (hs : SourceMarkState a pa) (z : ℝ) :
    0 ≤ envelope P d.L d.H d.hh d.dd d.B d.phi a pa r z := by
  have he : (negativeQuad P d 0 0 r).rayCheck=true ∧ (positiveQuad P d 0 0 r).rayCheck=true ∧
      (negativeQuad P d 0 1 r).rayCheck=true ∧ (positiveQuad P d 0 1 r).rayCheck=true ∧
      (negativeQuad P d 1 0 r).rayCheck=true ∧ (positiveQuad P d 1 0 r).rayCheck=true ∧
      (middleQuad P d r).unitCheck=true := by
    simpa only [endpointCheck, Bool.and_eq_true_iff, and_assoc] using h
  rcases he with ⟨hn00,hp00,hn01,hp01,hn10,hp10,hm⟩
  have hneg (a pa : ℚ) (ha : 0 ≤ a) (hh : (negativeQuad P d a pa r).rayCheck=true)
      (hz : z ≤ 0) : 0 ≤ envelope P d.L d.H d.hh d.dd d.B d.phi a pa r z := by
    have hx : 0 ≤ -z := by linarith
    have hq := Quad.rayCheck_sound hh hx
    rw [← negativeQuad_identity P d a pa r (-z) ha hx, neg_neg] at hq
    exact hq
  have hpos (a pa : ℚ) (ha : 0 ≤ a) (hh : (positiveQuad P d a pa r).rayCheck=true)
      (hz : (a : ℝ) ≤ z) : 0 ≤ envelope P d.L d.H d.hh d.dd d.B d.phi a pa r z := by
    have hx : 0 ≤ z-(a : ℝ) := sub_nonneg.mpr hz
    have hq := Quad.rayCheck_sound hh hx
    rw [← positiveQuad_identity P d a pa r (z-a) ha hx] at hq
    have he : (a : ℝ)+(z-a)=z := by ring
    rwa [he] at hq
  rcases hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · by_cases hz : z ≤ 0
    · simpa only [Rat.cast_zero] using hneg 0 0 (by norm_num) hn00 hz
    · simpa only [Rat.cast_zero] using hpos 0 0 (by norm_num) hp00 (by simpa using (le_of_not_ge hz))
  · by_cases hz : z ≤ 0
    · simpa only [Rat.cast_zero, Rat.cast_one] using hneg 0 1 (by norm_num) hn01 hz
    · simpa only [Rat.cast_zero, Rat.cast_one] using hpos 0 1 (by norm_num) hp01 (by simpa using (le_of_not_ge hz))
  · by_cases hz : z ≤ 0
    · simpa only [Rat.cast_zero, Rat.cast_one] using hneg 1 0 (by norm_num) hn10 hz
    · by_cases hz1 : 1 ≤ z
      · simpa only [Rat.cast_zero, Rat.cast_one] using hpos 1 0 (by norm_num) hp10 (by simpa using hz1)
      · have hx : 1-z ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith,by linarith⟩
        have hq := Quad.unitCheck_sound hm hx
        rw [← middleQuad_identity P d r hx] at hq
        have he : 1-(1-z)=z := by ring
        rwa [he] at hq
end Checker

def Bounds.check (d : Bounds) : Bool :=
  Checker.endpointCheck P d d.rl && Checker.endpointCheck P d d.rh

theorem Bounds.check_sound {d : Bounds} (h : d.check P=true)
    {a parentA r z : ℝ} (hs : SourceMarkState a parentA)
    (hr : (d.rl : ℝ) ≤ r) (hrh : r ≤ (d.rh : ℝ)) :
    0 ≤ envelope P d.L d.H d.hh d.dd d.B d.phi a parentA r z := by
  have hh : Checker.endpointCheck P d d.rl=true ∧
      Checker.endpointCheck P d d.rh=true := by
    simpa only [Bounds.check, Bool.and_eq_true_iff] using h
  have hlo := Checker.endpointCheck_sound P hh.1 hs z
  have hhi := Checker.endpointCheck_sound P hh.2 hs z
  by_cases he : (d.rl : ℝ) = d.rh
  · have hr' : r=(d.rl : ℝ) := by linarith
    rwa [hr']
  · have hpos : 0 < (d.rh : ℝ)-d.rl :=
      sub_pos.mpr (lt_of_le_of_ne (hr.trans hrh) he)
    have hid : envelope P d.L d.H d.hh d.dd d.B d.phi a parentA r z =
        (((d.rh : ℝ)-r)/((d.rh : ℝ)-d.rl))*envelope P d.L d.H d.hh d.dd d.B d.phi a parentA d.rl z +
        ((r-(d.rl : ℝ))/((d.rh : ℝ)-d.rl))*envelope P d.L d.H d.hh d.dd d.B d.phi a parentA d.rh z := by
      unfold envelope
      field_simp
      ring
    rw [hid]
    exact add_nonneg (mul_nonneg (div_nonneg (sub_nonneg.mpr hrh) hpos.le) hlo)
      (mul_nonneg (div_nonneg (sub_nonneg.mpr hr) hpos.le) hhi)

#print axioms Bounds.check_sound
end ForestUnimodality.ParametricSourceEnvelope
