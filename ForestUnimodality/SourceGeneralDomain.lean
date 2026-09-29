import ForestUnimodality.SourceEnvelopeGeneral
import ForestUnimodality.SourceGeneralCapacity
import ForestUnimodality.SourceScalarCells

/-! Shared parameter/domain witnesses and the real source-to-envelope map.
No fixed numerical price or activity interval is built into these definitions. -/
namespace ForestUnimodality.ParametricSource
open ParametricSourceEnvelope

structure Domain where
  lower : ℚ
  b : ℚ
  K : ℚ
  lowerLog : SourceLogWitness
  onePlusLog : SourceLogWitness
  kExp : ExpEnclosure.PowerCertificate
  kExpLo : ℚ
  kExpHi : ℚ

def Domain.Accepts (D : Domain) : Prop :=
  0<D.lower ∧ D.lower≤D.b ∧ 0<D.K ∧
  D.lowerLog.check D.lower=true ∧ D.onePlusLog.check (1+D.b)=true ∧
  D.kExp.check (1+D.K) D.kExpLo D.kExpHi=true ∧ D.b≤D.K*D.kExpLo

instance (D : Domain) : Decidable D.Accepts := by unfold Domain.Accepts; infer_instance

def Domain.check (D : Domain) : Bool := decide D.Accepts

structure Domain.Valid (D : Domain) : Prop where
  lower_pos : 0<(D.lower:ℝ)
  b_pos : 0<(D.b:ℝ)
  lower_le_b : (D.lower:ℝ)≤D.b
  K_pos : 0<(D.K:ℝ)
  capacity : (D.b:ℝ)≤D.K*Real.exp (1+(D.K:ℝ))
  lowerLog_lo : (D.lowerLog.lo:ℝ)≤Real.log (D.lower:ℝ)
  onePlusLog_hi : Real.log (1+(D.b:ℝ))≤(D.onePlusLog.hi:ℝ)

theorem Domain.check_sound {D : Domain} (h : D.check=true) : D.Valid := by
  have hd : D.Accepts := of_decide_eq_true h
  rcases hd with ⟨hl,hlb,hK,hlogl,hlogb,hexp,hcap⟩
  have hlr : (0:ℝ)<D.lower := by exact_mod_cast hl
  have hlbr : (D.lower:ℝ)≤D.b := by exact_mod_cast hlb
  have hKr : (0:ℝ)<D.K := by exact_mod_cast hK
  refine ⟨hlr,hlr.trans_le hlbr,hlbr,hKr,?_,
    (D.lowerLog.certificate.check_sound hlogl).1,?_⟩
  · have he := (D.kExp.check_sound hexp).1
    push_cast at he
    have hc : (D.b:ℝ)≤(D.K:ℝ)*(D.kExpLo:ℝ) := by exact_mod_cast hcap
    exact hc.trans (mul_le_mul_of_nonneg_left he hKr.le)
  · have he := (D.onePlusLog.certificate.check_sound hlogb).2
    simpa only [Rat.cast_add,Rat.cast_one] using he

/-- Every signed real response is preserved in this comparison. Only proved
lower/upper bounds of coefficients are substituted. -/
theorem envelope_le (P : RationalSourceParameters) (hP : P.toReal.Admissible)
    {lower b a parentA p r z L H hh dd B phi : ℝ}
    (hr0 : 0≤r) (hr1 : r≤1)
    (hcap : L≤1/(p*sourceLogCapacity b p) ∧ H≤1/sourceOddsCapacity b (sourceLogCapacity b p))
    (hlog : B≤-P.toReal.logPrice*(Real.log p-2*Real.log (1-p)-Real.log lower)/p)
    (hphi : phi≤sourcePhi lower b p) (hhh : 1-p/2≤hh) (hdd : 1-p≤dd) :
    envelope P L H hh dd B phi a parentA r z ≤
      sourceScalarRow P.toReal lower b a parentA p r z := by
  have hrc : 0≤1-r := by linarith
  have hu := hP.2.2.2.1
  have hv := hP.2.2.2.2
  have hmain : r*(1-p)*z^2≤r*dd*z^2 := by gcongr
  have hup : P.toReal.positivePrice a*L*(max 0 (a-z))^2 ≤
      P.toReal.positivePrice a*(1/(p*sourceLogCapacity b p))*(max 0 (a-z))^2 := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcap.1 (hu a)) (sq_nonneg _)
  have hvp : P.toReal.negativePrice a*L*(max 0 (z-a))^2 ≤
      P.toReal.negativePrice a*(1/(p*sourceLogCapacity b p))*(max 0 (z-a))^2 := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcap.1 (hv a)) (sq_nonneg _)
  have hum : P.toReal.positivePrice parentA*(1-p/2)*(max 0 z)^2 ≤
      P.toReal.positivePrice parentA*hh*(max 0 z)^2 := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhh (hu parentA)) (sq_nonneg _)
  have hvm : P.toReal.negativePrice parentA*(1-p/2)*(max 0 (-z))^2 ≤
      P.toReal.negativePrice parentA*hh*(max 0 (-z))^2 := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhh (hv parentA)) (sq_nonneg _)
  have hblock : r*((a-z)^2*H)-(1-r)*dd*z^2 ≤
      r*((a-z)^2/sourceOddsCapacity b (sourceLogCapacity b p))-(1-r)*(1-p)*z^2 := by
    rw [div_eq_mul_one_div ((a-z)^2)]
    apply sub_le_sub
    · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcap.2 (sq_nonneg _)) hr0
    · gcongr
  have hb := mul_le_mul_of_nonneg_left hblock hP.2.2.1
  have hph := mul_le_mul_of_nonneg_left
    (show r*(1+phi)-1≤r*(1+sourcePhi lower b p)-1 from sub_le_sub_right
      (mul_le_mul_of_nonneg_left (show 1+phi≤1+sourcePhi lower b p by linarith) hr0) 1) hP.2.1
  dsimp only [envelope,sourceScalarRow]
  rw [neg_mul,neg_div] at hlog
  have he : r*((a-z)^2*H)=r*(a-z)^2*H := by ring
  rw [he] at hb
  linarith

#print axioms Domain.check_sound
#print axioms envelope_le
end ForestUnimodality.ParametricSource

