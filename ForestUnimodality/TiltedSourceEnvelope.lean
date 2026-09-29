import ForestUnimodality.TiltedSourceCertificate
import ForestUnimodality.SourceEnvelopeGeneral

namespace ForestUnimodality.TiltedSource
open ParametricSourceEnvelope SourceEnvelopeCertificate
structure Parameters where
  C : ℚ
  u0 : ℚ
  u1 : ℚ
  v0 : ℚ
  v1 : ℚ

def Parameters.source (P : Parameters) : RationalSourceParameters :=
  ⟨0,P.C,P.u0,P.u1,P.v0,P.v1,0,0,0,0⟩
noncomputable def Parameters.toReal (P : Parameters) : TiltedSourceParameters :=
  ⟨P.C,(P.source.toReal).positivePrice,(P.source.toReal).negativePrice⟩
def Parameters.check (P : Parameters) : Bool :=
  decide (0<P.C ∧ 0≤P.u0 ∧ 0≤P.u1 ∧ 0≤P.v0 ∧ 0≤P.v1)
theorem Parameters.check_sound {P : Parameters} (hc : P.check=true) :
    P.toReal.Admissible ∧ 0<P.toReal.C := by
  have h : 0<P.C ∧ 0≤P.u0 ∧ 0≤P.u1 ∧ 0≤P.v0 ∧ 0≤P.v1 := of_decide_eq_true hc
  refine ⟨⟨?_,?_⟩,by change (0:ℝ)<P.C; exact_mod_cast h.1⟩ <;> intro a
  · dsimp only [Parameters.toReal,Parameters.source,RationalSourceParameters.toReal]
    split_ifs <;> exact_mod_cast (by first | exact h.2.2.1 | exact h.2.1)
  · dsimp only [Parameters.toReal,Parameters.source,RationalSourceParameters.toReal]
    split_ifs <;> exact_mod_cast (by first | exact h.2.2.2.2 | exact h.2.2.2.1)

def sourceMark (s : Fin 3) : ℚ := if s=2 then 1 else 0
def parentMark (s : Fin 3) : ℚ := if s=1 then 1 else 0

structure Bounds where
  L : ℚ
  hh : ℚ
  dd : ℚ
  rl : ℚ
  rh : ℚ

def Bounds.source (d : Bounds) : ParametricSourceEnvelope.Bounds := ⟨d.L,0,d.hh,d.dd,0,0,d.rl,d.rh⟩
noncomputable def envelope (P : Parameters) (d : Bounds) (a pa r z : ℝ) : ℝ :=
  ParametricSourceEnvelope.envelope P.source d.L 0 d.hh d.dd 0 0 a pa r z

theorem envelope_eq (P : Parameters) (d : Bounds) (a pa r z : ℝ) :
    envelope P d a pa r z=P.toReal.C*r*a-r*d.dd*z^2+
      P.toReal.positivePrice a*d.L*(max 0 (a-z))^2-
      P.toReal.positivePrice pa*d.hh*(max 0 z)^2+
      P.toReal.negativePrice a*d.L*(max 0 (z-a))^2-
      P.toReal.negativePrice pa*d.hh*(max 0 (-z))^2 := by
  simp only [envelope,ParametricSourceEnvelope.envelope,Parameters.source,Parameters.toReal,
    RationalSourceParameters.toReal,Rat.cast_zero,zero_add,zero_mul,add_zero]
  ring

def endpointCheck (P : Parameters) (s : Fin 3) (d : Bounds) (r : ℚ) : Bool :=
  (Checker.negativeQuad P.source d.source (sourceMark s) (parentMark s) r).rayCheck &&
  (Checker.positiveQuad P.source d.source (sourceMark s) (parentMark s) r).rayCheck &&
  (if s=2 then (Checker.middleQuad P.source d.source r).unitCheck else true)

theorem endpointCheck_sound {P : Parameters} {s : Fin 3} {d : Bounds} {r : ℚ}
    (hc : endpointCheck P s d r=true) (z : ℝ) :
    0≤envelope P d (sourceMark s) (parentMark s) r z := by
  have h : (Checker.negativeQuad P.source d.source (sourceMark s) (parentMark s) r).rayCheck=true ∧
      (Checker.positiveQuad P.source d.source (sourceMark s) (parentMark s) r).rayCheck=true ∧
      (if s=2 then (Checker.middleQuad P.source d.source r).unitCheck else true)=true := by
    simpa only [endpointCheck,Bool.and_eq_true_iff,and_assoc] using hc
  have ha : 0≤sourceMark s := by unfold sourceMark; split_ifs <;> norm_num
  by_cases hz : z≤0
  · have hh := Quad.rayCheck_sound h.1 (neg_nonneg.mpr hz)
    rw [←Checker.negativeQuad_identity P.source d.source (sourceMark s) (parentMark s) r (-z) ha (neg_nonneg.mpr hz),neg_neg] at hh
    simpa only [envelope,Bounds.source,Rat.cast_zero] using hh
  · by_cases hza : (sourceMark s:ℝ)≤z
    · have hh := Quad.rayCheck_sound h.2.1 (sub_nonneg.mpr hza)
      rw [←Checker.positiveQuad_identity P.source d.source (sourceMark s) (parentMark s) r (z-sourceMark s) ha (sub_nonneg.mpr hza)] at hh
      simpa only [envelope,Bounds.source,Rat.cast_zero,add_sub_cancel] using hh
    · have hs : s=2 := by
        by_contra hs
        have ha0 : (sourceMark s:ℝ)=0 := by simp [sourceMark,hs]
        rw [ha0] at hza
        exact hza (le_of_not_ge hz)
      subst s
      have hc' : (Checker.middleQuad P.source d.source r).unitCheck=true := by simpa using h.2.2
      have hx : 1-z∈Set.Icc (0:ℝ) 1 := by norm_num [sourceMark] at hza; constructor <;> linarith
      have hh := Quad.unitCheck_sound hc' hx
      rw [←Checker.middleQuad_identity P.source d.source r hx] at hh
      simpa only [envelope,Bounds.source,sourceMark,parentMark,ite_true,show (2:Fin 3)≠1 by decide,if_false,
        Rat.cast_one,Rat.cast_zero,sub_sub_cancel] using hh

def Bounds.check (d : Bounds) (P : Parameters) (s : Fin 3) : Bool :=
  endpointCheck P s d d.rl && endpointCheck P s d d.rh

theorem Bounds.check_sound {P : Parameters} {s : Fin 3} {d : Bounds}
    (hc : d.check P s=true) {r z : ℝ} (hr : (d.rl:ℝ)≤r) (hrh : r≤(d.rh:ℝ)) :
    0≤envelope P d (sourceMark s) (parentMark s) r z := by
  have h : endpointCheck P s d d.rl=true ∧ endpointCheck P s d d.rh=true := by
    simpa only [Bounds.check,Bool.and_eq_true_iff] using hc
  have hlo := endpointCheck_sound h.1 z
  have hhi := endpointCheck_sound h.2 z
  by_cases he : (d.rl:ℝ)=d.rh
  · have hrr : r=(d.rl:ℝ) := by linarith
    rwa [hrr]
  · have hp : 0<(d.rh:ℝ)-d.rl := sub_pos.mpr (lt_of_le_of_ne (hr.trans hrh) he)
    have hid : envelope P d (sourceMark s) (parentMark s) r z =
        (((d.rh:ℝ)-r)/((d.rh:ℝ)-d.rl))*envelope P d (sourceMark s) (parentMark s) d.rl z+
        ((r-(d.rl:ℝ))/((d.rh:ℝ)-d.rl))*envelope P d (sourceMark s) (parentMark s) d.rh z := by
      simp only [envelope_eq]
      field_simp
      ring
    rw [hid]
    exact add_nonneg (mul_nonneg (div_nonneg (sub_nonneg.mpr hrh) hp.le) hlo)
      (mul_nonneg (div_nonneg (sub_nonneg.mpr hr) hp.le) hhi)

theorem envelope_le (P : Parameters) (d : Bounds) (hc : P.check=true)
    (cap : ℝ→ℝ) {a pa p r z : ℝ} (hr : 0≤r)
    (hL : (d.L:ℝ)≤1/(p*sourceLogCapacity (cap a) p))
    (hh : 1-p/2≤(d.hh:ℝ)) (hd : 1-p≤(d.dd:ℝ)) :
    envelope P d a pa r z≤tiltedSourceRow P.toReal cap a pa p r z := by
  have hs := (Parameters.check_sound hc).1
  have hp := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL (hs.1 a)) (sq_nonneg (max 0 (a-z)))
  have hn := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL (hs.2 a)) (sq_nonneg (max 0 (z-a)))
  have hpp := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (hs.1 pa)) (sq_nonneg (max 0 z))
  have hnn := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (hs.2 pa)) (sq_nonneg (max 0 (-z)))
  have hdd := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd hr) (sq_nonneg z)
  rw [envelope_eq]
  unfold tiltedSourceRow
  linarith

#print axioms Bounds.check_sound
#print axioms envelope_le
end ForestUnimodality.TiltedSource
