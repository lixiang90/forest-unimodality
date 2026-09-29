import ForestUnimodality.AffineSourceEnvelope
import ForestUnimodality.SelectionSourceCells

namespace ForestUnimodality.AffineSource
open BernsteinCertificate

structure Domain where
  b : ℚ
  K : ℚ
  kExp : ExpEnclosure.PowerCertificate
  kExpLo : ℚ
  kExpHi : ℚ

def Domain.check (D : Domain) : Bool :=
  decide (0<D.b ∧ 0<D.K ∧ D.kExp.check (1+D.K) D.kExpLo D.kExpHi=true ∧ D.b≤D.K*D.kExpLo)

structure Domain.Valid (D : Domain) : Prop where
  b_pos : 0<(D.b:ℝ)
  K_pos : 0<(D.K:ℝ)
  capacity : (D.b:ℝ)≤D.K*Real.exp (1+(D.K:ℝ))

theorem Domain.check_sound {D : Domain} (hc : D.check=true) : D.Valid := by
  have h : 0<D.b ∧ 0<D.K ∧ D.kExp.check (1+D.K) D.kExpLo D.kExpHi=true ∧ D.b≤D.K*D.kExpLo :=
    of_decide_eq_true hc
  refine ⟨by exact_mod_cast h.1,by exact_mod_cast h.2.1,?_⟩
  have he := (D.kExp.check_sound h.2.2.1).1
  push_cast at he
  have hb : (D.b:ℝ)≤(D.K:ℝ)*(D.kExpLo:ℝ) := by exact_mod_cast h.2.2.2
  exact hb.trans (mul_le_mul_of_nonneg_left he (by exact_mod_cast h.2.1.le))

def probabilityCap (D : Domain) : ℚ := D.b/(1+D.b)

structure Cell where
  left : ℚ
  right : ℚ
  L : ℚ
  H : ℚ
  segment : ℕ
  logCapacity : SourceLogWitness
  pieces : List EnvelopeCertificate

def Cell.retentionLower (c : Cell) (D : Domain) : ℚ := 1/(1+D.b*(1-c.left))

def Cell.bounds (c : Cell) (P : Parameters) : Bounds :=
  ⟨P.A/c.right,c.L,c.H,1-c.left/2,1-c.left⟩

def Cell.CapacityAccepts (c : Cell) (D : Domain) : Prop :=
  if c.left=0 then
    c.right<probabilityCap D ∧ c.H=0 ∧
    c.logCapacity.check (D.b*(1-c.right)/c.right)=true ∧
    1/(1-c.right)≤c.logCapacity.lo ∧ c.L*(c.right*c.logCapacity.hi)≤1
  else
    c.logCapacity.check (D.b*(1-c.left)/c.left)=true ∧
    (c.L≤1/D.K ∨ c.L*(c.right*c.logCapacity.hi)≤1) ∧
    (1+D.b)^c.segment≤D.b*(1-c.left)/c.left ∧
    D.b*(1-c.left)/c.left<(1+D.b)^(c.segment+1) ∧
    c.H*((c.segment:ℚ)*D.b+(D.b*(1-c.left)/c.left)/(1+D.b)^c.segment-1)≤1

def Cell.Accepts (c : Cell) (P : Parameters) (D : Domain) : Prop :=
  0≤c.left ∧ c.left<c.right ∧ c.right≤probabilityCap D ∧ 0≤c.L ∧
  c.CapacityAccepts D ∧ c.retentionLower D<1 ∧
  c.pieces.all (fun t=>envelopeCheck t P (c.bounds P))=true ∧
  SourceIntervalCoverage.check (fun t=>t.lo) (fun t=>t.hi) (c.retentionLower D) 1 c.pieces=true

instance (c : Cell) (P : Parameters) (D : Domain) : Decidable (c.Accepts P D) := by
  unfold Cell.Accepts Cell.CapacityAccepts
  infer_instance

def Cell.check (c : Cell) (P : Parameters) (D : Domain) : Bool := decide (c.Accepts P D)

theorem Cell.check_sound {c : Cell} {P : Parameters} {D : Domain}
    (hc : c.check P D=true) (hD : D.Valid) (hP : P.check=true)
    {p r z : ℝ} (hp : 0<p) (hlp : (c.left:ℝ)≤p) (hpr : p≤(c.right:ℝ))
    (hpq : p<(D.b:ℝ)/(1+(D.b:ℝ)))
    (hr : 1/(1+(D.b:ℝ)*(1-p))≤r) (hr1 : r≤1) :
    0≤affineSourceRow P.toReal D.b p r 1 z := by
  have h : c.Accepts P D := of_decide_eq_true hc
  rcases h with ⟨hl,hlr,hrq,hL,hcap,hrl,hchecks,hcover⟩
  have hq1 : (D.b:ℝ)/(1+(D.b:ℝ))<1 := (div_lt_one (by linarith [hD.b_pos])).mpr (by linarith)
  have hleft : (0:ℝ)≤c.left := by exact_mod_cast hl
  have hLr : (0:ℝ)≤c.L := by exact_mod_cast hL
  have hcapacities : (c.L:ℝ)≤1/(p*sourceLogCapacity D.b p) ∧
      (c.H:ℝ)≤1/sourceOddsCapacity D.b (sourceLogCapacity D.b p) := by
    unfold Cell.CapacityAccepts at hcap
    by_cases hl0 : c.left=0
    · rw [if_pos hl0] at hcap
      rcases hcap with ⟨hrq',hHz,hlog,hlo,hh⟩
      have hlogr := c.logCapacity.certificate.check_sound hlog
      push_cast at hlogr
      have hrrq : (c.right:ℝ)<(D.b:ℝ)/(1+(D.b:ℝ)) := by
        unfold probabilityCap at hrq'
        exact_mod_cast hrq'
      have hlor : 1/(1-(c.right:ℝ))≤(c.logCapacity.lo:ℝ) := by exact_mod_cast hlo
      refine ⟨source_origin_capacity_lower hD.b_pos hp hpr hrrq (hlor.trans hlogr.1) hlogr.2 hLr
        (by exact_mod_cast hh),?_⟩
      rw [hHz,Rat.cast_zero]
      exact one_div_nonneg.mpr (sourceOddsCapacity_pos hD.b_pos (source_log_capacity_pos hD.b_pos hp hpq)).le
    · rw [if_neg hl0] at hcap
      rcases hcap with ⟨hlog,hLc,hjlo,hjhi,hH⟩
      have hlpos : (0:ℝ)<c.left := by exact_mod_cast lt_of_le_of_ne hl (Ne.symm hl0)
      have hlogr := (c.logCapacity.certificate.check_sound hlog).2
      push_cast at hlogr
      have hLc' : (c.L:ℝ)≤1/(D.K:ℝ) ∨ (c.L:ℝ)*((c.right:ℝ)*(c.logCapacity.hi:ℝ))≤1 := by
        rcases hLc with h | h
        · exact Or.inl (by exact_mod_cast h)
        · exact Or.inr (by exact_mod_cast h)
      exact source_cell_capacity_bounds_general c.segment hD.b_pos hD.K_pos hD.capacity
        hlpos hlp hpr hpq hlogr hLc' hLr (by exact_mod_cast hjlo) (by exact_mod_cast hjhi)
        (by exact_mod_cast hH)
  have hdenpos : 0<1+(D.b:ℝ)*(1-p) := by
    have ht := mul_nonneg hD.b_pos.le (by linarith [hpq.trans hq1] : 0≤1-p)
    linarith
  have hr0 : 0≤r := (div_nonneg (by norm_num) hdenpos.le).trans hr
  have hret : (c.retentionLower D:ℝ)≤r := by
    simp only [Cell.retentionLower,Rat.cast_div,Rat.cast_one,Rat.cast_add,Rat.cast_mul,Rat.cast_sub]
    apply le_trans ?_ hr
    apply one_div_le_one_div_of_le hdenpos
    have ht := mul_le_mul_of_nonneg_left hlp hD.b_pos.le
    linarith
  obtain ⟨piece,hmem,hlo,hhi⟩ := SourceIntervalCoverage.check_sound_closed
    (fun t : EnvelopeCertificate=>t.lo) (fun t=>t.hi) hcover hrl hret (by simpa using hr1)
  have he := envelopeCheck_sound ((List.all_eq_true.mp hchecks) piece hmem) (z:=z) ⟨hlo,hhi⟩
  apply he.trans
  apply envelope_le P (c.bounds P) hP hD.b_pos hp hr0 hr1
  · simp only [Cell.bounds,Rat.cast_div]
    exact div_le_div_of_nonneg_left (Parameters.check_sound hP).2.1 hp hpr
  · exact hcapacities
  · simp only [Cell.bounds,Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat]
    linarith
  · simp only [Cell.bounds,Rat.cast_sub,Rat.cast_one]
    linarith

#print axioms Domain.check_sound
#print axioms Cell.check_sound
end ForestUnimodality.AffineSource
