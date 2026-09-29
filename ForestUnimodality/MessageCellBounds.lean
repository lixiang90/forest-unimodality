import ForestUnimodality.MessageLogCertificate
import ForestUnimodality.MessageParentCertificate

/-! Computable probability-cell bounds for common spline message prices.
All transcendental substitutions, including the signed logarithmic penalty,
are proved for the actual probability throughout the cell. -/
namespace ForestUnimodality.MessageCells
open MessagePriceSpline
abbrev Domain := ParametricSource.Domain

structure CellBounds where
  base : SelectionSource.Cell
  hh : ℚ
  exactLog : SourceLogWitness
  prices : MessagePriceSpline.CellBounds
  logLower : ℚ

def CellBounds.Accepts (c : CellBounds) (P : Parameters) (D : Domain) : Prop :=
  D.lower=P.lower ∧ D.b=P.upper ∧
  0≤c.base.left ∧ c.base.left<c.base.right ∧ c.base.right≤SelectionSource.probabilityCap D ∧
  0≤c.base.L ∧ 0≤c.base.H ∧ 0≤c.hh ∧
  0≤c.prices.u ∧ 0≤c.prices.v ∧ 0≤c.prices.s ∧
  c.base.CapacityAccepts D ∧
  c.base.logRight.check c.base.right=true ∧ c.base.logComplement.check (1-c.base.right)=true ∧
  c.base.phi≤SelectionSource.probabilityCap D/D.onePlusLog.hi*
    max 0 (D.lowerLog.lo+c.base.logComplement.lo-c.base.logRight.hi) ∧
  (if c.base.left=0 then 1≤c.hh else
    c.exactLog.check (1/(1-c.base.left))=true ∧ c.base.left≤c.hh*c.exactLog.lo) ∧
  c.prices.check P c.base.left c.base.right=true ∧
  c.logLower*c.base.right≤P.Dn-P.ell*
    (c.base.logRight.hi-2*c.base.logComplement.lo-D.lowerLog.lo)

instance (c : CellBounds) (P : Parameters) (D : Domain) : Decidable (c.Accepts P D) := by
  unfold CellBounds.Accepts SelectionSource.Cell.CapacityAccepts
  infer_instance

def CellBounds.check (c : CellBounds) (P : Parameters) (D : Domain) : Bool := decide (c.Accepts P D)

structure CellBounds.Valid (c : CellBounds) (P : Parameters) (D : Domain) (p : ℝ) : Prop where
  lower_eq : D.lower=P.lower
  upper_eq : D.b=P.upper
  left_nonneg : 0≤(c.base.left:ℝ)
  right_lt_one : (c.base.right:ℝ)<1
  L_nonneg : 0≤(c.base.L:ℝ)
  H_nonneg : 0≤(c.base.H:ℝ)
  u_nonneg : 0≤(c.prices.u:ℝ)
  v_nonneg : 0≤(c.prices.v:ℝ)
  s_nonneg : 0≤(c.prices.s:ℝ)
  capacity : (c.base.L:ℝ)≤1/(p*sourceLogCapacity D.b p) ∧
    (c.base.H:ℝ)≤1/sourceOddsCapacity D.b (sourceLogCapacity D.b p)
  exactH : sourceExactH p≤(c.hh:ℝ)
  phi : (c.base.phi:ℝ)≤sourcePhi D.lower D.b p
  prices : c.prices.containsReal (evaluate P.pieces p)
  logarithm : (c.logLower:ℝ)≤sourceLogPenalty D.lower P.toReal.Dn P.toReal.ell p

theorem CellBounds.check_sound {c : CellBounds} {P : Parameters} {D : Domain}
    (hc : c.check P D=true) (hP : P.check=true) (hD : D.Valid)
    (hmono : 0≤P.toReal.Dn+P.toReal.ell*
      (1+Real.sqrt 2-Real.log ((1+Real.sqrt 2)/(2*(P.lower:ℝ)))))
    {p : ℝ} (hp : 0<p) (hlp : (c.base.left:ℝ)≤p) (hpr : p≤(c.base.right:ℝ))
    (hpq : p<(D.b:ℝ)/(1+(D.b:ℝ))) : c.Valid P D p := by
  have hc' : c.Accepts P D := of_decide_eq_true hc
  rcases hc' with ⟨hlo,hup,hl,hlr,hrq,hL,hH,hhh,hu,hv,hs,hcap,hlogR,hlogC,hphi,hexact,hprices,hlog⟩
  have hq1 : (D.b:ℝ)/(1+(D.b:ℝ))<1 :=
    (div_lt_one (by linarith [hD.b_pos])).mpr (by linarith)
  have hrightq : (c.base.right:ℝ)≤(D.b:ℝ)/(1+(D.b:ℝ)) := by
    unfold SelectionSource.probabilityCap at hrq
    exact_mod_cast hrq
  have hright1 := hrightq.trans_lt hq1
  have hleft : (0:ℝ)≤c.base.left := by exact_mod_cast hl
  have hLr : (0:ℝ)≤c.base.L := by exact_mod_cast hL
  have hlogRr := (c.base.logRight.certificate.check_sound hlogR).2
  have hlogCr := (c.base.logComplement.certificate.check_sound hlogC).1
  push_cast at hlogRr hlogCr
  refine ⟨hlo,hup,hleft,hright1,hLr,by exact_mod_cast hH,
    by exact_mod_cast hu,by exact_mod_cast hv,by exact_mod_cast hs,
    c.base.capacity_bounds hD hcap hleft hLr hp hlp hpr hpq,?_,?_,?_,?_⟩
  · apply sourceExactH_cell_upper hleft hlp (hpr.trans_lt hright1)
    by_cases hz : c.base.left=0
    · rw [if_pos hz] at hexact
      simpa [hz,sourceExactH] using
        (show (1:ℝ)≤(c.hh:ℝ) by exact_mod_cast hexact)
    · rw [if_neg hz] at hexact
      have hlpos : (0:ℝ)<c.base.left :=
        lt_of_le_of_ne hleft (Ne.symm (by exact_mod_cast hz))
      have he := (c.exactLog.certificate.check_sound hexact.1).1
      push_cast at he
      exact sourceExactH_upper_of_log_lower hlpos (hlp.trans hpr |>.trans_lt hright1)
        (by exact_mod_cast hhh) he (by exact_mod_cast hexact.2)
  · exact source_cell_phi_lower hD.lower_pos hD.b_pos hp (le_refl p) hpr hright1
      hlogRr hlogCr hD.lowerLog_lo hD.onePlusLog_hi (Φ:=(c.base.phi:ℝ)) (by
        unfold SelectionSource.probabilityCap at hphi
        exact_mod_cast hphi)
  · apply MessagePriceSpline.CellBounds.check_sound hP hprices
    · exact ⟨hp.le,by simpa only [hup] using hpq.le⟩
    · exact ⟨hlp,hpr⟩
  · apply sourceLogPenalty_cell_lower hD.lower_pos (Parameters.check_sound hP).2.2.2.2.2.1
      (by simpa only [hlo] using hmono) hp hpr hright1
    · exact sourceLogReference_upper hlogRr hlogCr hD.lowerLog_lo
    · dsimp only [Parameters.toReal]
      exact_mod_cast hlog

def CellBounds.envelopeBounds (c : CellBounds) (D : Domain) (second below : Bool) :
    MessagePolynomialEnvelope.Bounds :=
  ⟨c.base.L,c.base.H,c.hh,1-c.base.left,c.base.phi,
    SelectionSource.affineSlope (SelectionSource.probabilityCap D) c.base.left second,
    SelectionSource.affineIntercept (SelectionSource.probabilityCap D) second,c.logLower,
    c.prices.u,c.prices.v,c.prices.s,if below then c.prices.tauHi else c.prices.tauLo⟩

/-- The checked cell envelope lies below the true row for arbitrary signed
response and any three nonnegative common parent prices. -/
theorem CellBounds.Valid.marked_envelope_le {c : CellBounds} {P : Parameters} {D : Domain}
    {p : ℝ} (hc : c.Valid P D p) (hP : P.check=true) (hD : D.Valid)
    (second : Bool) {r d pu pv ps pt : ℝ} (hr0 : 0≤r) (hr1 : r≤1)
    (hlp : (c.base.left:ℝ)≤p) (hpu : 0≤pu) (hpv : 0≤pv) (hps : 0≤ps) :
    messageSourceMarkedEnvelope P.toReal
      (if d≤1 then (c.envelopeBounds D second true).toReal
       else (c.envelopeBounds D second false).toReal) r d pu pv ps pt ≤
      messageSourceMarkedRow P.toReal D.lower D.b p r d pu pv ps pt := by
  have hA := Parameters.check_sound hP
  have hpr := hc.prices
  have htau (below : Bool) (ht : below=true ↔ d≤1) :
      ((c.envelopeBounds D second below).toReal.tau)*(d-1)≤P.toReal.tau p*(d-1) := by
    cases below with
    | false =>
      have hd : 1≤d := le_of_not_ge (by simpa using ht)
      exact mul_le_mul_of_nonneg_right hpr.2.2.2.1 (sub_nonneg.mpr hd)
    | true =>
      have hd : d≤1 := ht.mp rfl
      exact mul_le_mul_of_nonpos_right hpr.2.2.2.2 (sub_nonpos.mpr hd)
  have hb (below : Bool) (ht : below=true ↔ d≤1) :
      messageSourceMarkedEnvelope P.toReal (c.envelopeBounds D second below).toReal r d pu pv ps pt ≤
        messageSourceMarkedRow P.toReal D.lower D.b p r d pu pv ps pt := by
    apply messageSourceMarkedEnvelope_le P.toReal _ _ _ _ _ _ _ _ _ _
      hA.2.2.1 hA.2.2.2.2.1 hr0 hr1 hc.L_nonneg hc.H_nonneg
      hc.u_nonneg hc.v_nonneg hc.s_nonneg hpr.1 hpr.2.1 hpr.2.2.1 hpu hpv hps
      hc.capacity.1 hc.capacity.2 hc.exactH
    · change 1-p≤((1-c.base.left:ℚ):ℝ)
      simp only [Rat.cast_sub,Rat.cast_one]
      linarith
    · exact hc.phi
    · exact SelectionSource.affine_lower D hD.b_pos c.base.left second hlp hr0
    · exact hc.logarithm
    · exact htau below ht
  split_ifs with hd
  · exact hb true (by simp [hd])
  · exact hb false (by simp only [Bool.false_eq_true,false_iff]; exact hd)

#print axioms CellBounds.check_sound
#print axioms CellBounds.Valid.marked_envelope_le
end ForestUnimodality.MessageCells
