import ForestUnimodality.SelectionSourceBounds
import ForestUnimodality.SourceGeneralCells
import ForestUnimodality.SourceIntervalCoverage

namespace ForestUnimodality.SourceIntervalCoverage

theorem check_sound_closed {α : Type*} (left right : α→ℚ) {lower upper : ℚ} {cells : List α}
    (h : check left right lower upper cells=true) (hlt : lower<upper) {p : ℝ}
    (hp : (lower:ℝ)≤p) (hpu : p≤(upper:ℝ)) :
    ∃c∈cells,(left c:ℝ)≤p ∧ p≤(right c:ℝ) := by
  by_cases he : p=(lower:ℝ)
  · subst p
    cases cells with
    | nil => exact (not_lt_of_ge (of_decide_eq_true h) hlt).elim
    | cons c cs =>
      have hh : (left c≤lower ∧ lower≤right c) ∧ check left right (right c) upper cs=true := by
        simpa only [check,Bool.and_eq_true_iff,decide_eq_true_eq] using h
      exact ⟨c,by simp,by exact_mod_cast hh.1.1,by exact_mod_cast hh.1.2⟩
  · exact check_sound left right h (lt_of_le_of_ne hp (Ne.symm he)) hpu
end ForestUnimodality.SourceIntervalCoverage

namespace ForestUnimodality.SelectionSource
open BernsteinCertificate
abbrev Domain := ParametricSource.Domain

def probabilityCap (D : Domain) : ℚ := D.b/(1+D.b)

structure Piece where
  second : Bool
  certificate : EnvelopeCertificate

def Piece.left (p : Piece) : ℚ := p.certificate.lo
def Piece.right (p : Piece) : ℚ := p.certificate.hi

structure Cell where
  left : ℚ
  right : ℚ
  L : ℚ
  H : ℚ
  phi : ℚ
  segment : ℕ
  logCapacity : SourceLogWitness
  logRight : SourceLogWitness
  logComplement : SourceLogWitness
  pieces : List Piece

def Cell.retentionLower (c : Cell) (D : Domain) : ℚ := 1/(1+D.b*(1-c.left))

def affineSlope (q pl : ℚ) (second : Bool) : ℚ :=
  if second then (1+q)/(2*q^2)*pl else (1+q)/(2*q)*pl

def affineIntercept (q : ℚ) (second : Bool) : ℚ :=
  if second then (q-1)/(2*q) else 0

def Cell.bounds (c : Cell) (D : Domain) (second : Bool) : Bounds :=
  ⟨c.L,c.H,1-c.left/2,1-c.left,c.phi,
    affineSlope (probabilityCap D) c.left second,affineIntercept (probabilityCap D) second⟩

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
  c.CapacityAccepts D ∧ c.logRight.check c.right=true ∧
  c.logComplement.check (1-c.right)=true ∧
  c.phi≤probabilityCap D/D.onePlusLog.hi*max 0 (D.lowerLog.lo+c.logComplement.lo-c.logRight.hi) ∧
  c.retentionLower D<1 ∧
  c.pieces.all (fun t=>t.certificate.check P (c.bounds D t.second))=true ∧
  SourceIntervalCoverage.check Piece.left Piece.right (c.retentionLower D) 1 c.pieces=true

instance instDecidableCellAccepts (c : Cell) (P : Parameters) (D : Domain) : Decidable (c.Accepts P D) := by
  unfold Cell.Accepts Cell.CapacityAccepts
  infer_instance

def Cell.check (c : Cell) (P : Parameters) (D : Domain) : Bool := decide (c.Accepts P D)

theorem affine_lower (D : Domain) (hb : 0<(D.b:ℝ)) (pl : ℚ) (second : Bool)
    {p r : ℝ} (hlp : (pl:ℝ)≤p) (hr : 0≤r) :
    (affineSlope (probabilityCap D) pl second:ℝ)*r+affineIntercept (probabilityCap D) second ≤
      MarginalSelectionBound.selectionFraction ((D.b:ℝ)/(1+(D.b:ℝ))) (p*r) := by
  have hq : 0<(D.b:ℝ)/(1+(D.b:ℝ)) := by positivity
  cases second
  · simpa only [affineSlope,affineIntercept,probabilityCap,Bool.false_eq_true,if_false,
      Rat.cast_mul,Rat.cast_div,Rat.cast_add,Rat.cast_one,Rat.cast_ofNat,Rat.cast_zero,add_zero]
      using selectionFraction_first_lower hq hlp hr
  · simpa only [affineSlope,affineIntercept,probabilityCap,if_true,
      Rat.cast_mul,Rat.cast_div,Rat.cast_add,Rat.cast_sub,Rat.cast_pow,Rat.cast_one,Rat.cast_ofNat]
      using selectionFraction_second_lower hq hlp hr

theorem Cell.check_sound {c : Cell} {P : Parameters} {D : Domain}
    (hc : c.check P D=true) (hD : D.Valid) (hP : P.check=true)
    {p r z : ℝ} (hp : 0<p) (hlp : (c.left:ℝ)≤p) (hpr : p≤(c.right:ℝ))
    (hpq : p<(D.b:ℝ)/(1+(D.b:ℝ)))
    (hr : 1/(1+(D.b:ℝ)*(1-p))≤r) (hr1 : r≤1) :
    0≤sourceSelectionScalarRow P.toReal D.lower D.b p r z := by
  have hh : c.Accepts P D := of_decide_eq_true hc
  rcases hh with ⟨hl,hlr,hrq,hL,hcap,hlogR,hlogC,hPhi,hrl,hchecks,hcover⟩
  have hq1 : (D.b:ℝ)/(1+(D.b:ℝ))<1 := (div_lt_one (by linarith [hD.b_pos])).mpr (by linarith)
  have hleft : (0:ℝ)≤c.left := by exact_mod_cast hl
  have hrightq : (c.right:ℝ)≤(D.b:ℝ)/(1+(D.b:ℝ)) := by
    unfold probabilityCap at hrq
    exact_mod_cast hrq
  have hright1 := hrightq.trans_lt hq1
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
        (by exact_mod_cast hh), ?_⟩
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
  have hlogRr := (c.logRight.certificate.check_sound hlogR).2
  have hlogCr := (c.logComplement.certificate.check_sound hlogC).1
  push_cast at hlogRr hlogCr
  have hphi := source_cell_phi_lower hD.lower_pos hD.b_pos hp (le_refl p) hpr hright1
    hlogRr hlogCr hD.lowerLog_lo hD.onePlusLog_hi (Φ:=(c.phi:ℝ)) (by
      unfold probabilityCap at hPhi
      exact_mod_cast hPhi)
  have hdenpos : 0<1+(D.b:ℝ)*(1-p) := by
    have hpos := mul_nonneg hD.b_pos.le (by linarith [hpq.trans hq1] : 0≤1-p)
    linarith
  have hr0 : 0≤r := (div_nonneg (by norm_num) hdenpos.le).trans hr
  have hret : (c.retentionLower D:ℝ)≤r := by
    simp only [Cell.retentionLower,Rat.cast_div,Rat.cast_one,Rat.cast_add,Rat.cast_mul,Rat.cast_sub]
    apply le_trans ?_ hr
    apply one_div_le_one_div_of_le hdenpos
    have hmul := mul_le_mul_of_nonneg_left hlp hD.b_pos.le
    linarith
  obtain ⟨piece,hmem,hlo,hhi⟩ := SourceIntervalCoverage.check_sound_closed Piece.left Piece.right
    hcover hrl hret (by simpa using hr1)
  have hen := EnvelopeCertificate.check_sound ((List.all_eq_true.mp hchecks) piece hmem) (z:=z) ⟨hlo,hhi⟩
  apply hen.trans
  apply envelope_le P (c.bounds D piece.second) (Parameters.check_sound hP).1
    (Parameters.check_sound hP).2.1 hr0 hr1
  · exact hcapacities
  · exact hphi
  · simp only [Cell.bounds,Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat]
    linarith
  · simp only [Cell.bounds,Rat.cast_sub,Rat.cast_one]
    linarith
  · exact affine_lower D hD.b_pos c.left piece.second hlp hr0

#print axioms Cell.check_sound
end ForestUnimodality.SelectionSource
