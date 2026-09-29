import ForestUnimodality.MessageCellBounds

/-! Complete finite retention and parent coverage for the spline/flow/log
message source rows. Positivity is supplied by rational certificates. -/
namespace ForestUnimodality.MessageCells
open MessagePriceSpline

def polynomialParameters (P : Parameters) : MessagePolynomialEnvelope.Parameters :=
  ⟨P.CJ,P.Cmu,P.w,P.t⟩

def CellBounds.parentCap (c : CellBounds) (D : Domain) : ℚ :=
  D.b*(1-c.base.left)/(1+D.b*(1-c.base.left))

structure ParentEntry where
  segment : Segment
  certificate : ParentSegmentCertificate

structure RetentionPiece where
  lo : ℚ
  hi : ℚ
  second : Bool
  parents : List ParentEntry

def RetentionPiece.check (w : RetentionPiece) (P : Parameters) (D : Domain) (c : CellBounds) : Bool :=
  decide (w.parents.map ParentEntry.segment=P.pieces) &&
    w.parents.all (fun e=>e.certificate.check e.segment (polynomialParameters P)
      (c.envelopeBounds D w.second true) (c.envelopeBounds D w.second false)
      w.lo w.hi (c.parentCap D))

theorem CellBounds.Valid.parent_cap_bounds {c : CellBounds} {P : Parameters} {D : Domain}
    {p : ℝ} (hc : c.Valid P D p) (hD : D.Valid)
    (hlp : (c.base.left:ℝ)≤p) (hpr : p≤(c.base.right:ℝ)) :
    (D.b:ℝ)*(1-p)/(1+(D.b:ℝ)*(1-p))≤(c.parentCap D:ℝ) ∧
    (c.parentCap D:ℝ)≤(P.upper:ℝ)/(1+(P.upper:ℝ)) := by
  have hp1 := hpr.trans_lt hc.right_lt_one
  have hl1 := hlp.trans_lt hp1
  have hb := hD.b_pos
  have hdenp : 0<1+(D.b:ℝ)*(1-p) := by positivity
  have hdenl : 0<1+(D.b:ℝ)*(1-(c.base.left:ℝ)) := by positivity
  have hcast : (c.parentCap D:ℝ)=
      (D.b:ℝ)*(1-(c.base.left:ℝ))/(1+(D.b:ℝ)*(1-(c.base.left:ℝ))) := by
    simp only [CellBounds.parentCap,Rat.cast_div,Rat.cast_mul,Rat.cast_sub,Rat.cast_one,Rat.cast_add]
  refine ⟨?_,?_⟩
  · rw [hcast]
    apply (div_le_div_iff₀ hdenp hdenl).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlp hb.le]
  · rw [hcast,←hc.upper_eq]
    exact sourceParentProbability_le_cap hb hc.left_nonneg hl1 (le_refl _)

theorem CellBounds.Valid.retention_lower {c : CellBounds} {P : Parameters} {D : Domain}
    {p r : ℝ} (hc : c.Valid P D p) (hD : D.Valid)
    (hlp : (c.base.left:ℝ)≤p) (hpr : p≤(c.base.right:ℝ))
    (hr : 1/(1+(D.b:ℝ)*(1-p))≤r) :
    (c.base.retentionLower D:ℝ)≤r ∧ 0≤r := by
  have hp1 := hpr.trans_lt hc.right_lt_one
  have hb := hD.b_pos
  have hd : 0<1+(D.b:ℝ)*(1-p) := by positivity
  refine ⟨?_,(div_nonneg (by norm_num) hd.le).trans hr⟩
  simp only [SelectionSource.Cell.retentionLower,Rat.cast_div,Rat.cast_one,
    Rat.cast_add,Rat.cast_mul,Rat.cast_sub]
  apply le_trans ?_ hr
  apply one_div_le_one_div_of_le hd
  nlinarith [mul_le_mul_of_nonneg_left hlp hb.le]

theorem RetentionPiece.check_sound {w : RetentionPiece} {P : Parameters} {D : Domain} {c : CellBounds}
    {p r z parentp : ℝ}
    (hw : w.check P D c=true) (hc : c.Valid P D p) (hP : P.check=true) (hD : D.Valid)
    (hlp : (c.base.left:ℝ)≤p) (hpr : p≤(c.base.right:ℝ))
    (hr : r∈Set.Icc (w.lo:ℝ) (w.hi:ℝ)) (hr0 : 0≤r) (hr1 : r≤1)
    (hparentLo : 1-r≤parentp) (hparentHi : parentp≤(c.parentCap D:ℝ)) :
    0≤messageSourceScalarRow P.toReal D.lower D.b p r z parentp := by
  have hh : w.parents.map ParentEntry.segment=P.pieces ∧
      w.parents.all (fun e=>e.certificate.check e.segment (polynomialParameters P)
        (c.envelopeBounds D w.second true) (c.envelopeBounds D w.second false)
        w.lo w.hi (c.parentCap D))=true := by
    simpa only [RetentionPiece.check,Bool.and_eq_true_iff,decide_eq_true_eq] using hw
  have hP' : P.Accepts := of_decide_eq_true hP
  apply P.scalar_nonneg_of_clipped_segments hP D.lower D.b p r z (1-r) (c.parentCap D) parentp
  · exact ⟨(sub_nonneg.mpr hr1).trans hparentLo,
      hparentHi.trans (hc.parent_cap_bounds hD hlp hpr).2⟩
  · exact hparentLo
  · exact hparentHi
  · intro seg hseg hinter
    have hmem : seg∈w.parents.map ParentEntry.segment := by rw [hh.1]; exact hseg
    obtain ⟨e,he,hes⟩ := List.mem_map.mp hmem
    have hecheck := (List.all_eq_true.mp hh.2) e he
    rw [hes] at hecheck
    have hen := ParentSegmentCertificate.check_sound hecheck P.toReal rfl rfl rfl rfl (z:=z) hr hinter
    have hsegcheck := (List.all_eq_true.mp hP'.2.2.2.2.2.2.1) seg hseg
    have hrow {x : ℝ} (hx : x∈Set.Icc (seg.lo:ℝ) (seg.hi:ℝ))
        (hen : 0≤signedMarkedEnvelope P.toReal (c.envelopeBounds D w.second true)
          (c.envelopeBounds D w.second false) r z seg x) :
        0≤messageSourceSegmentRow P.toReal D.lower D.b p r z seg x := by
      have hnon := Segment.check_sound hsegcheck hx
      apply hen.trans
      exact hc.marked_envelope_le hP hD w.second hr0 hr1 hlp hnon.1 hnon.2.1 hnon.2.2
    exact ⟨hrow ⟨le_max_left _ _,hinter.trans (min_le_left _ _)⟩ hen.1,
      hrow ⟨(le_max_left _ _).trans hinter,min_le_left _ _⟩ hen.2⟩

structure Cell where
  bounds : CellBounds
  pieces : List RetentionPiece

def Cell.check (c : Cell) (P : Parameters) (D : Domain) : Bool :=
  c.bounds.check P D && decide (c.bounds.base.retentionLower D<1) &&
    c.pieces.all (fun w=>w.check P D c.bounds) &&
    SourceIntervalCoverage.check RetentionPiece.lo RetentionPiece.hi
      (c.bounds.base.retentionLower D) 1 c.pieces

theorem Cell.check_sound {c : Cell} {P : Parameters} {D : Domain}
    (hc : c.check P D=true) (hP : P.check=true) (hD : D.Valid)
    (hmono : 0≤P.toReal.Dn+P.toReal.ell*
      (1+Real.sqrt 2-Real.log ((1+Real.sqrt 2)/(2*(P.lower:ℝ)))))
    {p r z parentp : ℝ} (hp : 0<p) (hlp : (c.bounds.base.left:ℝ)≤p)
    (hpr : p≤(c.bounds.base.right:ℝ)) (hpq : p<(D.b:ℝ)/(1+(D.b:ℝ)))
    (hr : 1/(1+(D.b:ℝ)*(1-p))≤r) (hr1 : r≤1)
    (hparentLo : 1-r≤parentp)
    (hparentHi : parentp≤(D.b:ℝ)*(1-p)/(1+(D.b:ℝ)*(1-p))) :
    0≤messageSourceScalarRow P.toReal D.lower D.b p r z parentp := by
  have hh : c.bounds.check P D=true ∧ c.bounds.base.retentionLower D<1 ∧
      c.pieces.all (fun w=>w.check P D c.bounds)=true ∧
      SourceIntervalCoverage.check RetentionPiece.lo RetentionPiece.hi
        (c.bounds.base.retentionLower D) 1 c.pieces=true := by
    simpa only [Cell.check,Bool.and_eq_true_iff,decide_eq_true_eq,and_assoc] using hc
  have hv := CellBounds.check_sound hh.1 hP hD hmono hp hlp hpr hpq
  have hret := hv.retention_lower hD hlp hpr hr
  obtain ⟨w,hw,hrl,hrh⟩ := SourceIntervalCoverage.check_sound_closed
    RetentionPiece.lo RetentionPiece.hi hh.2.2.2 hh.2.1 hret.1 (by simpa using hr1)
  exact RetentionPiece.check_sound ((List.all_eq_true.mp hh.2.2.1) w hw) hv hP hD hlp hpr
    ⟨hrl,hrh⟩ hret.2 hr1 hparentLo (hparentHi.trans (hv.parent_cap_bounds hD hlp hpr).1)

#print axioms RetentionPiece.check_sound
#print axioms Cell.check_sound
end ForestUnimodality.MessageCells
