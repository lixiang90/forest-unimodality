import ForestUnimodality.SelectionEnvelope
import ForestUnimodality.SourceGeneralDomain

namespace ForestUnimodality.SelectionSource
open MarginalSelectionBound

/-- Only the exact rational multiplier signs used by the real comparison. -/
def Parameters.Accepts (P : Parameters) : Prop :=
  0≤P.CJ ∧ 0≤P.Cmu ∧ 0≤P.u ∧ 0≤P.v ∧ 0≤P.w ∧ 0≤P.s
instance instDecidableAccepts (P : Parameters) : Decidable P.Accepts := by
  unfold Parameters.Accepts
  infer_instance
def Parameters.check (P : Parameters) : Bool := decide P.Accepts

theorem Parameters.check_sound {P : Parameters} (h : P.check=true) :
    P.toReal.Admissible ∧ 0≤P.toReal.CJ ∧ 0≤P.toReal.Cmu := by
  have hh : P.Accepts := of_decide_eq_true h
  rcases hh with ⟨hCJ,hCmu,hu,hv,hw,hs⟩
  refine ⟨⟨?_,?_,?_,?_⟩,?_,?_⟩ <;> dsimp only [Parameters.toReal]
  all_goals exact_mod_cast (by first | exact hu | exact hv | exact hw | exact hs | exact hCJ | exact hCmu)

/-- The two affine pieces always bound the max defining selectionFraction
from below. No branch membership is silently presumed at a grid point. -/
theorem selectionFraction_first_lower {q pl p r : ℝ} (hq : 0<q)
    (hlp : pl≤p) (hr : 0≤r) :
    ((1+q)/(2*q)*pl)*r≤selectionFraction q (p*r) := by
  have hm := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlp hr)
    (by positivity : 0≤(1+q)/(2*q))
  have hh := le_max_left ((1+q)/(2*q)*(p*r)) ((1+q)/(2*q^2)*(p*r)+(q-1)/(2*q))
  unfold selectionFraction
  nlinarith

theorem selectionFraction_second_lower {q pl p r : ℝ} (hq : 0<q)
    (hlp : pl≤p) (hr : 0≤r) :
    ((1+q)/(2*q^2)*pl)*r+(q-1)/(2*q)≤selectionFraction q (p*r) := by
  have hm := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlp hr)
    (by positivity : 0≤(1+q)/(2*q^2))
  have hh := le_max_right ((1+q)/(2*q)*(p*r)) ((1+q)/(2*q^2)*(p*r)+(q-1)/(2*q))
  unfold selectionFraction
  nlinarith

def Parameters.asMarked (P : Parameters) : RationalSourceParameters :=
  ⟨P.Cmu,0,P.u,P.u,P.v,P.v,P.w,P.t+P.w,P.s,0⟩

theorem Parameters.asMarked_toReal (P : Parameters) :
    P.asMarked.toReal=P.toReal.base := by
  unfold Parameters.asMarked RationalSourceParameters.toReal Parameters.toReal SelectionSourceParameters.base
  simp only [ite_self,Rat.cast_zero,Rat.cast_add]

theorem Parameters.asMarked_admissible {P : Parameters} (hP : P.toReal.Admissible) :
    P.asMarked.toReal.Admissible := by
  rw [P.asMarked_toReal]
  refine ⟨le_rfl,hP.2.2.1,hP.2.2.2,(fun _=>hP.1),(fun _=>hP.2.1)⟩

theorem envelope_eq_marked (P : Parameters) (d : Bounds) (r z : ℝ) :
    envelope P d r z=
      ParametricSourceEnvelope.envelope P.asMarked d.L d.H d.hh d.dd 0 d.phi 1 1 r z+
      (P.CJ:ℝ)*r*((d.fs:ℝ)*r+d.fb) := by
  unfold envelope ParametricSourceEnvelope.envelope Parameters.asMarked
  simp only [RationalSourceParameters.toReal,ite_self,Rat.cast_zero,Rat.cast_add]
  ring

/-- Complete real comparison of a frozen probability envelope with the true
selection source row. The supplied scalar bounds are later certified by logs
and exact capacity arithmetic; the unbounded response is not sampled. -/
theorem envelope_le (P : Parameters) (d : Bounds) (hP : P.toReal.Admissible)
    (hCJ : 0≤P.toReal.CJ) {lower b p r z : ℝ} (hr0 : 0≤r) (hr1 : r≤1)
    (hcap : (d.L:ℝ)≤1/(p*sourceLogCapacity b p) ∧
      (d.H:ℝ)≤1/sourceOddsCapacity b (sourceLogCapacity b p))
    (hphi : (d.phi:ℝ)≤sourcePhi lower b p)
    (hhh : 1-p/2≤(d.hh:ℝ)) (hdd : 1-p≤(d.dd:ℝ))
    (hf : (d.fs:ℝ)*r+d.fb≤selectionFraction (b/(1+b)) (p*r)) :
    envelope P d r z≤sourceSelectionScalarRow P.toReal lower b p r z := by
  have hb := ParametricSource.envelope_le P.asMarked (Parameters.asMarked_admissible hP)
    (a:=1) (parentA:=1) (B:=0) (z:=z) hr0 hr1 hcap
    (by simp [Parameters.asMarked,RationalSourceParameters.toReal]) hphi hhh hdd
  rw [P.asMarked_toReal] at hb
  have hf' := mul_le_mul_of_nonneg_left hf (mul_nonneg hCJ hr0)
  rw [envelope_eq_marked,sourceSelectionScalarRow_eq_base P.toReal lower b p r z 1]
  exact add_le_add hb hf'

#print axioms Parameters.check_sound
#print axioms selectionFraction_first_lower
#print axioms selectionFraction_second_lower
#print axioms envelope_le
end ForestUnimodality.SelectionSource
