import ForestUnimodality.SourceGeneralDomain
import ForestUnimodality.FullSourceEnvelope

/-! Rational certificates for the two exceptional probability regions:
an interval reaching arbitrarily close to zero, and the true leaf endpoint. -/
namespace ForestUnimodality.FullParametricSource
open ParametricSource
open ParametricSourceEnvelope

structure Origin where
  delta : ℚ
  logRatio : SourceLogWitness
  logRight : SourceLogWitness
  logComplement : SourceLogWitness
  bounds : Bounds

def Origin.Accepts (c : Origin) (P : RationalSourceParameters) (D : Domain) : Prop :=
  0<c.delta ∧ c.delta<D.b/(1+D.b) ∧
  c.logRatio.check (D.b*(1-c.delta)/c.delta)=true ∧
  c.logRight.check c.delta=true ∧ c.logComplement.check (1-c.delta)=true ∧
  1/(1-c.delta)≤c.logRatio.lo ∧ 0≤c.bounds.L ∧ c.bounds.L*(c.delta*c.logRatio.hi)≤1 ∧
  c.bounds.H=0 ∧
  c.bounds.phi≤(D.b/(1+D.b))/D.onePlusLog.hi*max 0 (D.lowerLog.lo+c.logComplement.lo-c.logRight.hi) ∧ c.bounds.hh=1 ∧ c.bounds.dd=1 ∧
  c.bounds.rl≤1/(1+D.b) ∧ 1≤c.bounds.rh ∧ 0≤c.bounds.B ∧
  c.bounds.B*c.delta≤-P.ell*(c.logRight.hi-2*c.logComplement.lo-D.lowerLog.lo) ∧
  FullSourceEnvelope.check P c.bounds=true

instance (c : Origin) (P : RationalSourceParameters) (D : Domain) : Decidable (c.Accepts P D) := by
  unfold Origin.Accepts
  infer_instance

def Origin.check (c : Origin) (P : RationalSourceParameters) (D : Domain) : Bool := decide (c.Accepts P D)

theorem Origin.check_sound {c : Origin} {P : RationalSourceParameters} {D : Domain}
    (hc : c.check P D=true) (hP : P.toReal.Admissible) (hD : D.Valid)
    {p r z : ℝ}
    (hp : 0<p) (hpδ : p≤(c.delta:ℝ))
    (hr : 1/(1+(D.b:ℝ)*(1-p))≤r) (hr1 : r≤1) :
    0≤sourceScalarRow P.toReal D.lower D.b 1 1 p r z := by
  have hc' : c.Accepts P D := of_decide_eq_true hc
  rcases hc' with ⟨hδ,hδq,hlogT,hlogR,hlogC,hTlo,hL,hLbound,hH,hphi,hhh,hdd,hrl,hrh,hB,hBbound,hcheck⟩
  have hδr : (0:ℝ)<c.delta := by exact_mod_cast hδ
  have hδqr : (c.delta:ℝ)<D.b/(1+(D.b:ℝ)) := by exact_mod_cast hδq
  have hδ1 : (c.delta:ℝ)<1 := hδqr.trans ((div_lt_one (by linarith [hD.b_pos] : 0<1+(D.b:ℝ))).mpr (by linarith))
  have hpq := hpδ.trans_lt hδqr
  have hp1 := hpδ.trans_lt hδ1
  have hlogTr := c.logRatio.certificate.check_sound hlogT
  have hlogRr := (c.logRight.certificate.check_sound hlogR).2
  have hlogCr := (c.logComplement.certificate.check_sound hlogC).1
  push_cast at hlogTr hlogCr
  have hTlor : 1/(1-(c.delta:ℝ))≤(c.logRatio.lo:ℝ) := by exact_mod_cast hTlo
  have hLr : (0:ℝ)≤c.bounds.L := by exact_mod_cast hL
  have hcapL := source_origin_capacity_lower hD.b_pos hp hpδ hδqr
    (hTlor.trans hlogTr.1) hlogTr.2 hLr (by exact_mod_cast hLbound)
  have hcapH : (0:ℝ)≤1/sourceOddsCapacity D.b (sourceLogCapacity D.b p) :=
    one_div_nonneg.mpr (sourceOddsCapacity_pos hD.b_pos (source_log_capacity_pos hD.b_pos hp hpq)).le
  have hlogp := (Real.log_le_log hp hpδ).trans hlogRr
  have hlogc := hlogCr.trans (Real.log_le_log (sub_pos.mpr hδ1) (by linarith : 1-(c.delta:ℝ)≤1-p))
  have hN : -(P.ell:ℝ)*(c.logRight.hi-2*(c.logComplement.lo:ℝ)-(D.lowerLog.lo:ℝ)) ≤
      -(P.ell:ℝ)*(Real.log p-2*Real.log (1-p)-Real.log (D.lower:ℝ)) := by
    exact mul_le_mul_of_nonpos_left (by linarith [hD.lowerLog_lo]) (neg_nonpos.mpr hP.1)
  have hBr : (0:ℝ)≤c.bounds.B := by exact_mod_cast hB
  have hBbr : (c.bounds.B:ℝ)*(c.delta:ℝ)≤
      -(P.ell:ℝ)*(c.logRight.hi-2*(c.logComplement.lo:ℝ)-(D.lowerLog.lo:ℝ)) := by exact_mod_cast hBbound
  have hlog : (c.bounds.B:ℝ)≤-P.toReal.logPrice*(Real.log p-2*Real.log (1-p)-Real.log (D.lower:ℝ))/p := by
    apply (le_div_iff₀ hp).mpr
    exact ((mul_le_mul_of_nonneg_left hpδ hBr).trans hBbr).trans hN
  have hden : 0<1+(D.b:ℝ)*(1-p) := by nlinarith [mul_pos hD.b_pos (sub_pos.mpr hp1)]
  have hret : 1/(1+(D.b:ℝ))≤r :=
    (one_div_le_one_div_of_le hden (by nlinarith [mul_nonneg hD.b_pos.le hp.le])).trans hr
  have hrlr : (c.bounds.rl:ℝ)≤1/(1+(D.b:ℝ)) := by exact_mod_cast hrl
  have hr0 : 0≤r := (div_nonneg (by norm_num) (by linarith [hD.b_pos] : 0≤1+(D.b:ℝ))).trans hret
  have hphibound : (c.bounds.phi:ℝ)≤sourcePhi D.lower D.b p :=
    source_cell_phi_lower hD.lower_pos hD.b_pos hp le_rfl hpδ hδ1
      hlogRr hlogCr hD.lowerLog_lo hD.onePlusLog_hi (by exact_mod_cast hphi)
  have he := FullSourceEnvelope.check_sound P hcheck (z:=z) (hrlr.trans hret) (hr1.trans (by exact_mod_cast hrh))
  apply he.trans
  apply envelope_le P hP hr0 hr1
  · exact ⟨hcapL, by simpa only [hH, Rat.cast_zero] using hcapH⟩
  · exact hlog
  · exact hphibound
  · simpa only [hhh, Rat.cast_one] using (by linarith : 1-p/2≤(1:ℝ))
  · simpa only [hdd, Rat.cast_one] using (by linarith : 1-p≤(1:ℝ))

structure Leaf where
  logRight : SourceLogWitness
  logComplement : SourceLogWitness
  B : ℚ
  rl : ℚ
  rh : ℚ

def Leaf.bounds (c : Leaf) (D : Domain) : Bounds where
  L := 0
  H := 0
  hh := 1-(D.b/(1+D.b))/2
  dd := 1-D.b/(1+D.b)
  B := c.B
  phi := 0
  rl := c.rl
  rh := c.rh

def Leaf.value (c : Leaf) (P : RationalSourceParameters) (D : Domain) (a pa r : ℚ) : ℚ :=
  (Checker.positiveQuad P (c.bounds D) a pa r).C

def Leaf.endpointCheck (c : Leaf) (P : RationalSourceParameters) (D : Domain) (r : ℚ) : Bool :=
  decide (0≤c.value P D 1 1 r)

def Leaf.Accepts (c : Leaf) (P : RationalSourceParameters) (D : Domain) : Prop :=
  c.logRight.check (D.b/(1+D.b))=true ∧
  c.logComplement.check (1-D.b/(1+D.b))=true ∧
  c.B*(D.b/(1+D.b))≤-P.ell*(c.logRight.hi-2*c.logComplement.lo-D.lowerLog.lo) ∧
  c.rl≤1/(1+D.b*(1-D.b/(1+D.b))) ∧ 1≤c.rh ∧
  c.endpointCheck P D c.rl=true ∧ c.endpointCheck P D c.rh=true

instance (c : Leaf) (P : RationalSourceParameters) (D : Domain) : Decidable (c.Accepts P D) := by
  unfold Leaf.Accepts
  infer_instance

def Leaf.check (c : Leaf) (P : RationalSourceParameters) (D : Domain) : Bool := decide (c.Accepts P D)

theorem Leaf.endpointCheck_sound {c : Leaf} {P : RationalSourceParameters} {D : Domain} {r : ℚ}
    (hc : c.endpointCheck P D r=true) :
    0≤envelope P (c.bounds D).L (c.bounds D).H (c.bounds D).hh (c.bounds D).dd
      (c.bounds D).B (c.bounds D).phi 1 1 r 1 := by
  have hh : 0≤c.value P D 1 1 r := of_decide_eq_true hc
  have hi := Checker.positiveQuad_identity P (c.bounds D) 1 1 r 0 (by norm_num) (by norm_num)
  simp only [Rat.cast_one,add_zero,zero_pow (by decide : 2≠0),mul_zero,zero_add] at hi
  rw [hi]
  exact_mod_cast hh

theorem Leaf.check_sound {c : Leaf} {P : RationalSourceParameters} {D : Domain}
    (hc : c.check P D=true) (hP : P.toReal.Admissible) (hD : D.Valid)
    {r : ℝ}
    (hr : 1/(1+(D.b:ℝ)*(1-(D.b:ℝ)/(1+(D.b:ℝ))))≤r) (hr1 : r≤1) :
    0≤sourceScalarRow P.toReal D.lower D.b 1 1 ((D.b:ℝ)/(1+(D.b:ℝ))) r 1 := by
  have hc' : c.Accepts P D := of_decide_eq_true hc
  rcases hc' with ⟨hlogR,hlogC,hB,hrl,hrh,hlo,hhi⟩
  let q : ℝ := (D.b:ℝ)/(1+(D.b:ℝ))
  have hb1 : 0<1+(D.b:ℝ) := by linarith [hD.b_pos]
  have hq : 0<q := div_pos hD.b_pos hb1
  have hq1 : q<1 := (div_lt_one hb1).mpr (by linarith)
  have hden : 0<1+(D.b:ℝ)*(1-q) := by nlinarith [mul_pos hD.b_pos (sub_pos.mpr hq1)]
  have hr0 : 0≤r := (div_nonneg (by norm_num) hden.le).trans hr
  have hrlr : (c.rl:ℝ)≤1/(1+(D.b:ℝ)*(1-q)) := by dsimp [q]; exact_mod_cast hrl
  have hlr := hrlr.trans hr
  have hrr : r≤(c.rh:ℝ) := hr1.trans (by exact_mod_cast hrh)
  have hlo' := Leaf.endpointCheck_sound hlo
  have hhi' := Leaf.endpointCheck_sound hhi
  have henv : 0≤envelope P (c.bounds D).L (c.bounds D).H (c.bounds D).hh (c.bounds D).dd
      (c.bounds D).B (c.bounds D).phi 1 1 r 1 := by
    by_cases he : (c.rl:ℝ)=c.rh
    · have hr' : r=(c.rl:ℝ) := by linarith
      rwa [hr']
    · have hpos : 0<(c.rh:ℝ)-c.rl := sub_pos.mpr (lt_of_le_of_ne (hlr.trans hrr) he)
      have hid : envelope P (c.bounds D).L (c.bounds D).H (c.bounds D).hh (c.bounds D).dd
          (c.bounds D).B (c.bounds D).phi 1 1 r 1 =
          (((c.rh:ℝ)-r)/((c.rh:ℝ)-c.rl))*envelope P (c.bounds D).L (c.bounds D).H (c.bounds D).hh (c.bounds D).dd
            (c.bounds D).B (c.bounds D).phi 1 1 c.rl 1 +
          ((r-(c.rl:ℝ))/((c.rh:ℝ)-c.rl))*envelope P (c.bounds D).L (c.bounds D).H (c.bounds D).hh (c.bounds D).dd
            (c.bounds D).B (c.bounds D).phi 1 1 c.rh 1 := by
        unfold envelope
        field_simp
        ring
      rw [hid]
      exact add_nonneg (mul_nonneg (div_nonneg (sub_nonneg.mpr hrr) hpos.le) hlo')
        (mul_nonneg (div_nonneg (sub_nonneg.mpr hlr) hpos.le) hhi')
  have hlogRr := (c.logRight.certificate.check_sound hlogR).2
  have hlogCr := (c.logComplement.certificate.check_sound hlogC).1
  push_cast at hlogRr hlogCr
  have hBr : (c.B:ℝ)*q≤-(P.ell:ℝ)*(c.logRight.hi-2*(c.logComplement.lo:ℝ)-(D.lowerLog.lo:ℝ)) := by
    dsimp [q]
    exact_mod_cast hB
  have hlog : (c.B:ℝ)≤-P.toReal.logPrice*(Real.log q-2*Real.log (1-q)-Real.log (D.lower:ℝ))/q := by
    apply (le_div_iff₀ hq).mpr
    apply hBr.trans
    apply mul_le_mul_of_nonpos_left ?_ (neg_nonpos.mpr hP.1)
    linarith [hD.lowerLog_lo]
  have hT : sourceLogCapacity D.b q=0 := by
    unfold sourceLogCapacity
    have he : (D.b:ℝ)*(1-q)/q=1 := by
      dsimp [q]
      field_simp [hD.b_pos.ne', hb1.ne']
      ring
    rw [he, Real.log_one]
  have hcap : (0:ℝ)≤1/(q*sourceLogCapacity D.b q) ∧
      (0:ℝ)≤1/sourceOddsCapacity D.b (sourceLogCapacity D.b q) := by
    simp [hT, sourceOddsCapacity]
  have hphinonneg : 0≤sourcePhi D.lower D.b q := by
    unfold sourcePhi
    apply mul_nonneg
    · exact div_nonneg (div_nonneg hD.b_pos.le hb1.le) (Real.log_pos (by linarith [hD.b_pos])).le
    · exact le_max_left _ _
  apply henv.trans
  apply envelope_le P hP hr0 hr1
  · simpa only [Leaf.bounds, Rat.cast_zero] using hcap
  · exact hlog
  · simpa only [Leaf.bounds, Rat.cast_zero] using hphinonneg
  · simp only [Leaf.bounds, Rat.cast_sub, Rat.cast_one, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
    rfl
  · simp only [Leaf.bounds, Rat.cast_sub, Rat.cast_one, Rat.cast_div, Rat.cast_add]
    rfl

#print axioms Origin.check_sound
#print axioms Leaf.check_sound
end ForestUnimodality.FullParametricSource
