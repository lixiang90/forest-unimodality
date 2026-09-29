import ForestUnimodality.SourceEnvelopeGeneral
import ForestUnimodality.FullMarkedSource
namespace ForestUnimodality.FullSourceEnvelope
open ParametricSourceEnvelope
open SourceEnvelopeCertificate
variable (P : RationalSourceParameters)

def middleQuad (d : Bounds) (r : ℚ) : Quad where
  A := -r*d.dd+P.u1*d.L-P.u1*d.hh+P.s*(r*d.H-(1-r)*d.dd)
  B := 2*r*d.dd+2*P.u1*d.hh-P.t+2*P.s*(1-r)*d.dd
  C := (Checker.positiveQuad P d 1 1 r).C

theorem middleQuad_identity (d : Bounds) (r : ℚ) {x : ℝ} (hx : x∈Set.Icc (0:ℝ) 1) :
    envelope P d.L d.H d.hh d.dd d.B d.phi 1 1 r (1-x)=
      ((middleQuad P d r).A:ℝ)*x^2+((middleQuad P d r).B:ℝ)*x+(middleQuad P d r).C := by
  have h1 : 1-(1-x)=x := by ring
  have h2 : 1-x-1= -x := by ring
  simp only [envelope,h1,h2,max_eq_left (neg_nonpos.mpr hx.1),
    max_eq_left (neg_nonpos.mpr (sub_nonneg.mpr hx.2)),max_eq_right hx.1,
    max_eq_right (sub_nonneg.mpr hx.2),middleQuad,Checker.positiveQuad]
  norm_num [Checker.posPrice,Checker.negPrice,RationalSourceParameters.toReal]
  ring

def endpointCheck (d : Bounds) (r : ℚ) : Bool :=
  (Checker.negativeQuad P d 1 1 r).rayCheck &&
  (Checker.positiveQuad P d 1 1 r).rayCheck && (middleQuad P d r).unitCheck

theorem endpointCheck_sound {d : Bounds} {r : ℚ} (h : endpointCheck P d r=true) (z : ℝ) :
    0≤envelope P d.L d.H d.hh d.dd d.B d.phi 1 1 r z := by
  have hh : (Checker.negativeQuad P d 1 1 r).rayCheck=true ∧
      (Checker.positiveQuad P d 1 1 r).rayCheck=true ∧ (middleQuad P d r).unitCheck=true := by
    simpa only [endpointCheck,Bool.and_eq_true_iff,and_assoc] using h
  by_cases hz : z≤0
  · have hq := Quad.rayCheck_sound hh.1 (show 0≤-z by linarith)
    rw [←Checker.negativeQuad_identity P d 1 1 r (-z) (by norm_num) (by linarith),neg_neg] at hq
    simpa only [Rat.cast_one] using hq
  · by_cases hz1 : 1≤z
    · have hq := Quad.rayCheck_sound hh.2.1 (show 0≤z-1 by linarith)
      rw [←Checker.positiveQuad_identity P d 1 1 r (z-1) (by norm_num) (by linarith)] at hq
      simpa only [Rat.cast_one,add_sub_cancel] using hq
    · have hx : 1-z∈Set.Icc (0:ℝ) 1 := ⟨by linarith,by linarith⟩
      have hq := Quad.unitCheck_sound hh.2.2 hx
      rw [←middleQuad_identity P d r hx] at hq
      simpa only [sub_sub_cancel] using hq

def check (d : Bounds) : Bool := endpointCheck P d d.rl && endpointCheck P d d.rh

theorem check_sound {d : Bounds} (h : check P d=true) {r z : ℝ}
    (hr : (d.rl:ℝ)≤r) (hrh : r≤(d.rh:ℝ)) :
    0≤envelope P d.L d.H d.hh d.dd d.B d.phi 1 1 r z := by
  have hh : endpointCheck P d d.rl=true ∧ endpointCheck P d d.rh=true := by
    simpa only [check,Bool.and_eq_true_iff] using h
  have hlo := endpointCheck_sound P hh.1 z
  have hhi := endpointCheck_sound P hh.2 z
  by_cases he : (d.rl:ℝ)=d.rh
  · have hr' : r=(d.rl:ℝ) := by linarith
    rwa [hr']
  · have hpos : 0<(d.rh:ℝ)-d.rl := sub_pos.mpr (lt_of_le_of_ne (hr.trans hrh) he)
    have hid : envelope P d.L d.H d.hh d.dd d.B d.phi 1 1 r z =
        (((d.rh:ℝ)-r)/((d.rh:ℝ)-d.rl))*envelope P d.L d.H d.hh d.dd d.B d.phi 1 1 d.rl z+
        ((r-(d.rl:ℝ))/((d.rh:ℝ)-d.rl))*envelope P d.L d.H d.hh d.dd d.B d.phi 1 1 d.rh z := by
      unfold envelope
      field_simp
      ring
    rw [hid]
    exact add_nonneg (mul_nonneg (div_nonneg (sub_nonneg.mpr hrh) hpos.le) hlo)
      (mul_nonneg (div_nonneg (sub_nonneg.mpr hr) hpos.le) hhi)

#print axioms check_sound
end ForestUnimodality.FullSourceEnvelope
