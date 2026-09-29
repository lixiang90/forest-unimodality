import ForestUnimodality.SourceGeneralDomain

namespace ForestUnimodality.ParametricSource
open ParametricSourceEnvelope

structure Cell where
  left : ℚ
  right : ℚ
  segment : ℕ
  logRatio : SourceLogWitness
  logRight : SourceLogWitness
  logComplement : SourceLogWitness
  bounds : Bounds

def Cell.logNumerator (P : RationalSourceParameters) (D : Domain) (c : Cell) : ℚ :=
  -P.ell*(c.logRight.hi-2*c.logComplement.lo-D.lowerLog.lo)

def Cell.Accepts (P : RationalSourceParameters) (D : Domain) (c : Cell) : Prop :=
  0<c.left ∧ c.left<c.right ∧ c.right≤D.b/(1+D.b) ∧
  c.logRatio.check (D.b*(1-c.left)/c.left)=true ∧
  c.logRight.check c.right=true ∧ c.logComplement.check (1-c.right)=true ∧
  0≤c.bounds.L ∧ (c.bounds.L≤1/D.K ∨ c.bounds.L*(c.right*c.logRatio.hi)≤1) ∧
  c.bounds.H*((c.segment:ℚ)*D.b+(D.b*(1-c.left)/c.left)/(1+D.b)^c.segment-1)≤1 ∧
  (1+D.b)^c.segment≤D.b*(1-c.left)/c.left ∧ D.b*(1-c.left)/c.left<(1+D.b)^(c.segment+1) ∧
  1-c.left/2≤c.bounds.hh ∧ 1-c.left≤c.bounds.dd ∧
  c.bounds.rl≤1/(1+D.b*(1-c.left)) ∧ 1≤c.bounds.rh ∧
  c.bounds.B≤c.logNumerator P D/(if 0≤c.logNumerator P D then c.right else c.left) ∧
  c.bounds.phi≤(D.b/(1+D.b))/D.onePlusLog.hi*max 0 (D.lowerLog.lo+c.logComplement.lo-c.logRight.hi) ∧
  c.bounds.check P=true

instance instDecidableCellAccepts (P : RationalSourceParameters) (D : Domain) (c : Cell) : Decidable (c.Accepts P D) := by
  unfold Cell.Accepts
  infer_instance

def Cell.check (P : RationalSourceParameters) (D : Domain) (c : Cell) : Bool := decide (c.Accepts P D)

theorem Cell.check_sound (P : RationalSourceParameters) (D : Domain)
    (hD : D.Valid) (hPa : P.admissibleCheck=true) {c : Cell} (hc : c.check P D=true)
    {a parentA p r z : ℝ} (hs : SourceMarkState a parentA)
    (hplp : (c.left:ℝ)≤p) (hpph : p≤(c.right:ℝ)) (hpq : p<(D.b:ℝ)/(1+(D.b:ℝ)))
    (hr : 1/(1+(D.b:ℝ)*(1-p))≤r) (hr1 : r≤1) :
    0≤sourceScalarRow P.toReal D.lower D.b a parentA p r z := by
  have hP := P.admissible_sound hPa
  have h : c.Accepts P D := of_decide_eq_true hc
  rcases h with ⟨hpl,hplt,hph,hlogT,hlogR,hlogC,hL0,hL,hH,hjlo,hjhi,hhh,hdd,hrl,hrh,hB,hPhi,hcheck⟩
  have hplr : (0:ℝ)<c.left := by exact_mod_cast hpl
  have hp : 0<p := hplr.trans_le hplp
  have hphr : (c.right:ℝ)≤(D.b:ℝ)/(1+(D.b:ℝ)) := by exact_mod_cast hph
  have hq1 : (D.b:ℝ)/(1+(D.b:ℝ))<1 :=
    (div_lt_one (by linarith [hD.b_pos])).mpr (by linarith)
  have hph1 : (c.right:ℝ)<1 := hphr.trans_lt hq1
  have hlogTr := (c.logRatio.certificate.check_sound hlogT).2
  have hlogRr := (c.logRight.certificate.check_sound hlogR).2
  have hlogCr := (c.logComplement.certificate.check_sound hlogC).1
  push_cast at hlogTr hlogCr
  have hcap := source_cell_capacity_bounds_general (L:=(c.bounds.L:ℝ)) (H:=(c.bounds.H:ℝ))
    (ph:=(c.right:ℝ)) (tUpper:=(c.logRatio.hi:ℝ)) c.segment hD.b_pos hD.K_pos hD.capacity
    hplr hplp hpph hpq hlogTr (by exact_mod_cast hL) (by exact_mod_cast hL0)
    (by exact_mod_cast hjlo) (by exact_mod_cast hjhi) (by exact_mod_cast hH)
  have hBN : (c.bounds.B:ℝ)≤(-(P.ell:ℝ)*(c.logRight.hi-2*c.logComplement.lo-(D.lowerLog.lo:ℝ))) /
      (if 0≤-(P.ell:ℝ)*(c.logRight.hi-2*c.logComplement.lo-(D.lowerLog.lo:ℝ)) then (c.right:ℝ) else (c.left:ℝ)) := by
    unfold Cell.logNumerator at hB
    by_cases hn : 0≤-P.ell*(c.logRight.hi-2*c.logComplement.lo-D.lowerLog.lo)
    · have hn' : (0:ℝ)≤-(P.ell:ℝ)*(c.logRight.hi-2*c.logComplement.lo-(D.lowerLog.lo:ℝ)) := by exact_mod_cast hn
      rw [if_pos hn] at hB
      rw [if_pos hn']
      exact_mod_cast hB
    · have hn' : ¬(0:ℝ)≤-(P.ell:ℝ)*(c.logRight.hi-2*c.logComplement.lo-(D.lowerLog.lo:ℝ)) := by exact_mod_cast hn
      rw [if_neg hn] at hB
      rw [if_neg hn']
      exact_mod_cast hB
  have hell : (0:ℝ)≤P.ell := hP.1
  have hlog := source_cell_log_bonus_general hell hplr hplp hpph hph1 hlogRr hlogCr hD.lowerLog_lo hBN
  have hphi := source_cell_phi_lower hD.lower_pos hD.b_pos hplr hplp hpph hph1
    hlogRr hlogCr hD.lowerLog_lo hD.onePlusLog_hi
    (Φ:=(c.bounds.phi:ℝ)) (by exact_mod_cast hPhi)
  have hrlr : (c.bounds.rl:ℝ)≤1/(1+(D.b:ℝ)*(1-(c.left:ℝ))) := by exact_mod_cast hrl
  have hret : (c.bounds.rl:ℝ)≤r := by
    apply hrlr.trans
    apply le_trans ?_ hr
    apply one_div_le_one_div_of_le
    · have hpos := mul_nonneg hD.b_pos.le (by linarith [hpq.trans hq1] : 0≤1-p)
      linarith
    · have hmul := mul_le_mul_of_nonneg_left hplp hD.b_pos.le
      linarith
  have hrhi : r≤(c.bounds.rh:ℝ) := hr1.trans (by exact_mod_cast hrh)
  have hr0 : 0≤r := by
    apply le_trans (div_nonneg (by norm_num) ?_) hr
    have hpos := mul_nonneg hD.b_pos.le (by linarith [hpq.trans hq1] : 0≤1-p)
    linarith
  have hhh' : 1-p/2≤(c.bounds.hh:ℝ) := by
    have hh : 1-(c.left:ℝ)/2≤c.bounds.hh := by exact_mod_cast hhh
    linarith
  have hdd' : 1-p≤(c.bounds.dd:ℝ) := by
    have hh : 1-(c.left:ℝ)≤c.bounds.dd := by exact_mod_cast hdd
    linarith
  exact (Bounds.check_sound P hcheck hs hret hrhi).trans (envelope_le P hP hr0 hr1 hcap hlog hphi hhh' hdd')

#print axioms Cell.check_sound
end ForestUnimodality.ParametricSource

