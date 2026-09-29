import ForestUnimodality.ExactSelectionSourceBounds
import ForestUnimodality.MessageSourceCellBounds

namespace ForestUnimodality.ExactSelectionSource
open SelectionSource

def exactHCheck (p hh : ℚ) (log : SourceLogWitness) : Bool := decide
  (0 ≤ p ∧ p < 1 ∧ 0 ≤ hh ∧
    (if p = 0 then 1 ≤ hh else
      log.check (1 / (1-p)) = true ∧ p ≤ hh * log.lo))

theorem exactHCheck_sound {p hh : ℚ} {log : SourceLogWitness}
    (hc : exactHCheck p hh log = true) : sourceExactH (p : ℝ) ≤ (hh : ℝ) := by
  have h : 0 ≤ p ∧ p < 1 ∧ 0 ≤ hh ∧
      (if p = 0 then 1 ≤ hh else log.check (1/(1-p)) = true ∧ p ≤ hh*log.lo) :=
    of_decide_eq_true hc
  by_cases hp0 : p = 0
  · rw [if_pos hp0] at h
    have hh1 : (1 : ℝ) ≤ hh := by exact_mod_cast h.2.2.2
    simpa [hp0, sourceExactH] using hh1
  · rw [if_neg hp0] at h
    have hp : (0 : ℝ) < p := by exact_mod_cast lt_of_le_of_ne h.1 (Ne.symm hp0)
    have hlog := (log.certificate.check_sound h.2.2.2.1).1
    push_cast at hlog
    exact sourceExactH_upper_of_log_lower hp (by exact_mod_cast h.2.1)
      (by exact_mod_cast h.2.2.1) hlog (by exact_mod_cast h.2.2.2.2)

structure Cell where
  base : SelectionSource.Cell
  hh : ℚ
  exactLog : SourceLogWitness

def Cell.left (c : Cell) : ℚ := c.base.left
def Cell.right (c : Cell) : ℚ := c.base.right

def Cell.bounds (c : Cell) (D : Domain) (second : Bool) : Bounds :=
  { c.base.bounds D second with hh := c.hh }

def Cell.Accepts (c : Cell) (P : Parameters) (D : Domain) : Prop :=
  0 ≤ c.base.left ∧ c.base.left < c.base.right ∧ c.base.right ≤ probabilityCap D ∧
  0 ≤ c.base.L ∧ 0 ≤ c.base.H ∧
  c.base.CapacityAccepts D ∧ exactHCheck c.base.left c.hh c.exactLog = true ∧
  c.base.logRight.check c.base.right = true ∧
  c.base.logComplement.check (1-c.base.right) = true ∧
  c.base.phi ≤ probabilityCap D / D.onePlusLog.hi *
    max 0 (D.lowerLog.lo + c.base.logComplement.lo - c.base.logRight.hi) ∧
  c.base.retentionLower D < 1 ∧
  c.base.pieces.all (fun t => t.certificate.check P (c.bounds D t.second)) = true ∧
  SourceIntervalCoverage.check Piece.left Piece.right (c.base.retentionLower D) 1 c.base.pieces = true

instance (c : Cell) (P : Parameters) (D : Domain) : Decidable (c.Accepts P D) := by
  unfold Cell.Accepts SelectionSource.Cell.CapacityAccepts
  infer_instance

def Cell.check (c : Cell) (P : Parameters) (D : Domain) : Bool := decide (c.Accepts P D)

theorem Cell.check_sound {c : Cell} {P : Parameters} {D : Domain}
    (hc : c.check P D = true) (hD : D.Valid) (hP : P.check = true)
    {p r z parentp : ℝ} (hp : 0 < p) (hlp : (c.left : ℝ) ≤ p) (hpr : p ≤ (c.right : ℝ))
    (hpq : p < (D.b : ℝ)/(1+(D.b : ℝ)))
    (hr : 1/(1+(D.b : ℝ)*(1-p)) ≤ r) (hr1 : r ≤ 1) :
    0 ≤ messageSourceScalarRow (toMessage P) D.lower D.b p r z parentp := by
  change (c.base.left : ℝ) ≤ p at hlp
  change p ≤ (c.base.right : ℝ) at hpr
  have hh : c.Accepts P D := of_decide_eq_true hc
  rcases hh with ⟨hl, hlr, hrq, hL, hH, hcap, hHexact, hlogR, hlogC, hPhi, hrl, hchecks, hcover⟩
  have hq1 : (D.b : ℝ)/(1+(D.b : ℝ)) < 1 :=
    (div_lt_one (by linarith [hD.b_pos])).mpr (by linarith)
  have hleft : (0 : ℝ) ≤ c.base.left := by exact_mod_cast hl
  have hrightq : (c.base.right : ℝ) ≤ (D.b : ℝ)/(1+(D.b : ℝ)) := by
    unfold probabilityCap at hrq
    exact_mod_cast hrq
  have hright1 := hrightq.trans_lt hq1
  have hLr : (0 : ℝ) ≤ c.base.L := by exact_mod_cast hL
  have hHr : (0 : ℝ) ≤ c.base.H := by exact_mod_cast hH
  have hcapacities := c.base.capacity_bounds hD hcap hleft hLr hp hlp hpr hpq
  have hlogRr := (c.base.logRight.certificate.check_sound hlogR).2
  have hlogCr := (c.base.logComplement.certificate.check_sound hlogC).1
  push_cast at hlogRr hlogCr
  have hphi := source_cell_phi_lower hD.lower_pos hD.b_pos hp (le_refl p) hpr hright1
    hlogRr hlogCr hD.lowerLog_lo hD.onePlusLog_hi (Φ := (c.base.phi : ℝ)) (by
      unfold probabilityCap at hPhi
      exact_mod_cast hPhi)
  have hdenpos : 0 < 1+(D.b : ℝ)*(1-p) := by
    have hpos := mul_nonneg hD.b_pos.le (by linarith [hpq.trans hq1] : 0 ≤ 1-p)
    linarith
  have hr0 : 0 ≤ r := (div_nonneg (by norm_num) hdenpos.le).trans hr
  have hret : (c.base.retentionLower D : ℝ) ≤ r := by
    simp only [SelectionSource.Cell.retentionLower, Rat.cast_div, Rat.cast_one, Rat.cast_add, Rat.cast_mul, Rat.cast_sub]
    apply le_trans ?_ hr
    apply one_div_le_one_div_of_le hdenpos
    have hmul := mul_le_mul_of_nonneg_left hlp hD.b_pos.le
    linarith
  obtain ⟨piece, hmem, hlo, hhi⟩ := SourceIntervalCoverage.check_sound_closed Piece.left Piece.right
    hcover hrl hret (by simpa using hr1)
  have hen := EnvelopeCertificate.check_sound ((List.all_eq_true.mp hchecks) piece hmem) (z := z) ⟨hlo,hhi⟩
  apply hen.trans
  apply ExactSelectionSource.envelope_le P (c.bounds D piece.second) hP hr0 hr1 hLr hHr
  · exact hcapacities
  · exact hphi
  · exact sourceExactH_cell_upper hleft hlp (hpq.trans hq1) (exactHCheck_sound hHexact)
  · simp only [Cell.bounds, SelectionSource.Cell.bounds, Rat.cast_sub, Rat.cast_one]
    change 1-p ≤ 1-(c.base.left : ℝ)
    exact sub_le_sub_left hlp 1
  · exact affine_lower D hD.b_pos c.base.left piece.second hlp hr0

#print axioms exactHCheck_sound
#print axioms Cell.check_sound
end ForestUnimodality.ExactSelectionSource
