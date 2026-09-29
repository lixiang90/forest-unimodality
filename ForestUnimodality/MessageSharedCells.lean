import ForestUnimodality.MessageCells
import ForestUnimodality.MessageSharedEndpoint

/-! Share a response's zero-endpoint certificate throughout a complete cell.
Only witnesses change; every geometric bound and original checker is retained. -/
namespace ForestUnimodality.MessagePolynomialEnvelope

def Certificate.shareEndpoint (c : Certificate) : Certificate :=
  { c with middle := { c.middle with left := c.negative.endpoint } }

theorem Certificate.check_shareEndpoint {c : Certificate} {P : Parameters}
    {Bbelow Babove : Bounds} {Q : ParentPrices} {lo hi : ℚ}
    (h : c.sharedEndpointCheck P Bbelow Babove Q lo hi = true) :
    c.shareEndpoint.check P Bbelow Babove Q lo hi = true := by
  apply Certificate.check_of_shared_endpoint (by rfl)
  exact h

end ForestUnimodality.MessagePolynomialEnvelope

namespace ForestUnimodality.MessagePriceSpline

def ParentBranchCertificate.shareEndpoint (w : ParentBranchCertificate) : ParentBranchCertificate :=
  ⟨w.lower.shareEndpoint, w.upper.shareEndpoint⟩

def ParentBranchCertificate.sharedEndpointCheck (w : ParentBranchCertificate) (c : Segment)
    (P : MessagePolynomialEnvelope.Parameters) (Bbelow Babove : MessagePolynomialEnvelope.Bounds)
    (rl rh cap : ℚ) (moving : Bool) : Bool :=
  if c.lo ≤ c.parentUpper cap ∧ c.branchLeft rl cap moving ≤ c.branchRight rh moving then
    w.lower.sharedEndpointCheck P Bbelow Babove
      (c.parentPolynomials (c.parentA moving) (Segment.parentB moving))
      (c.branchLeft rl cap moving) (c.branchRight rh moving) &&
    w.upper.sharedEndpointCheck P Bbelow Babove (c.parentPolynomials (c.parentUpper cap) 0)
      (c.branchLeft rl cap moving) (c.branchRight rh moving)
  else true

theorem ParentBranchCertificate.check_shareEndpoint {w : ParentBranchCertificate} {c : Segment}
    {P : MessagePolynomialEnvelope.Parameters} {Bbelow Babove : MessagePolynomialEnvelope.Bounds}
    {rl rh cap : ℚ} {moving : Bool}
    (h : w.sharedEndpointCheck c P Bbelow Babove rl rh cap moving = true) :
    w.shareEndpoint.check c P Bbelow Babove rl rh cap moving = true := by
  unfold ParentBranchCertificate.sharedEndpointCheck at h
  unfold ParentBranchCertificate.check
  split_ifs with ha
  · rw [if_pos ha] at h
    have hh := Bool.and_eq_true_iff.mp h
    exact Bool.and_eq_true_iff.mpr
      ⟨MessagePolynomialEnvelope.Certificate.check_shareEndpoint hh.1,
       MessagePolynomialEnvelope.Certificate.check_shareEndpoint hh.2⟩
  · rfl

def ParentSegmentCertificate.shareEndpoint (w : ParentSegmentCertificate) : ParentSegmentCertificate :=
  ⟨w.fixed.shareEndpoint, w.moving.shareEndpoint⟩

def ParentSegmentCertificate.sharedEndpointCheck (w : ParentSegmentCertificate) (c : Segment)
    (P : MessagePolynomialEnvelope.Parameters) (Bbelow Babove : MessagePolynomialEnvelope.Bounds)
    (rl rh cap : ℚ) : Bool :=
  w.fixed.sharedEndpointCheck c P Bbelow Babove rl rh cap false &&
    w.moving.sharedEndpointCheck c P Bbelow Babove rl rh cap true

theorem ParentSegmentCertificate.check_shareEndpoint {w : ParentSegmentCertificate} {c : Segment}
    {P : MessagePolynomialEnvelope.Parameters} {Bbelow Babove : MessagePolynomialEnvelope.Bounds}
    {rl rh cap : ℚ}
    (h : w.sharedEndpointCheck c P Bbelow Babove rl rh cap = true) :
    w.shareEndpoint.check c P Bbelow Babove rl rh cap = true := by
  have hh := Bool.and_eq_true_iff.mp h
  exact Bool.and_eq_true_iff.mpr
    ⟨ParentBranchCertificate.check_shareEndpoint hh.1,
     ParentBranchCertificate.check_shareEndpoint hh.2⟩

end ForestUnimodality.MessagePriceSpline

namespace ForestUnimodality.SourceIntervalCoverage

theorem check_map_preserving_bounds {α β : Type*} (f : α → β)
    (left right : α → ℚ) (left' right' : β → ℚ)
    (hl : ∀ x, left' (f x) = left x) (hr : ∀ x, right' (f x) = right x)
    (cells : List α) (lower upper : ℚ) :
    check left' right' lower upper (cells.map f) = check left right lower upper cells := by
  induction cells generalizing lower with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons, check, hl, hr, ih]

end ForestUnimodality.SourceIntervalCoverage

namespace ForestUnimodality.MessageCells
open MessagePriceSpline

def ParentEntry.shareEndpoint (e : ParentEntry) : ParentEntry :=
  ⟨e.segment, e.certificate.shareEndpoint⟩

def RetentionPiece.shareEndpoint (w : RetentionPiece) : RetentionPiece :=
  { w with parents := w.parents.map ParentEntry.shareEndpoint }

def RetentionPiece.sharedEndpointCheck (w : RetentionPiece) (P : Parameters)
    (D : Domain) (c : CellBounds) : Bool :=
  decide (w.parents.map ParentEntry.segment = P.pieces) &&
    w.parents.all (fun e => e.certificate.sharedEndpointCheck e.segment (polynomialParameters P)
      (c.envelopeBounds D w.second true) (c.envelopeBounds D w.second false)
      w.lo w.hi (c.parentCap D))

theorem RetentionPiece.check_shareEndpoint {w : RetentionPiece} {P : Parameters}
    {D : Domain} {c : CellBounds} (h : w.sharedEndpointCheck P D c = true) :
    w.shareEndpoint.check P D c = true := by
  have hh : w.parents.map ParentEntry.segment = P.pieces ∧
      w.parents.all (fun e => e.certificate.sharedEndpointCheck e.segment (polynomialParameters P)
        (c.envelopeBounds D w.second true) (c.envelopeBounds D w.second false)
        w.lo w.hi (c.parentCap D)) = true := by
    simpa only [RetentionPiece.sharedEndpointCheck, Bool.and_eq_true_iff, decide_eq_true_eq] using h
  simp only [RetentionPiece.check, Bool.and_eq_true_iff, decide_eq_true_eq]
  constructor
  · simpa only [RetentionPiece.shareEndpoint, List.map_map, Function.comp_def,
      ParentEntry.shareEndpoint] using hh.1
  · apply List.all_eq_true.mpr
    intro e he
    obtain ⟨original, ho, rfl⟩ := List.mem_map.mp he
    exact ParentSegmentCertificate.check_shareEndpoint ((List.all_eq_true.mp hh.2) original ho)

def Cell.shareEndpoint (c : Cell) : Cell :=
  { c with pieces := c.pieces.map RetentionPiece.shareEndpoint }

def Cell.sharedEndpointCheck (c : Cell) (P : Parameters) (D : Domain) : Bool :=
  c.bounds.check P D && decide (c.bounds.base.retentionLower D < 1) &&
    c.pieces.all (fun w => w.sharedEndpointCheck P D c.bounds) &&
    SourceIntervalCoverage.check RetentionPiece.lo RetentionPiece.hi
      (c.bounds.base.retentionLower D) 1 c.pieces

theorem Cell.check_shareEndpoint {c : Cell} {P : Parameters} {D : Domain}
    (h : c.sharedEndpointCheck P D = true) : c.shareEndpoint.check P D = true := by
  have hh : c.bounds.check P D = true ∧ c.bounds.base.retentionLower D < 1 ∧
      c.pieces.all (fun w => w.sharedEndpointCheck P D c.bounds) = true ∧
      SourceIntervalCoverage.check RetentionPiece.lo RetentionPiece.hi
        (c.bounds.base.retentionLower D) 1 c.pieces = true := by
    simpa only [Cell.sharedEndpointCheck, Bool.and_eq_true_iff, decide_eq_true_eq, and_assoc] using h
  simp only [Cell.check, Cell.shareEndpoint, Bool.and_eq_true_iff, decide_eq_true_eq, and_assoc]
  refine ⟨hh.1, hh.2.1, ?_, ?_⟩
  · apply List.all_eq_true.mpr
    intro w hw
    obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hw
    exact RetentionPiece.check_shareEndpoint ((List.all_eq_true.mp hh.2.2.1) original ho)
  · rw [SourceIntervalCoverage.check_map_preserving_bounds RetentionPiece.shareEndpoint
      RetentionPiece.lo RetentionPiece.hi RetentionPiece.lo RetentionPiece.hi
      (fun _ => rfl) (fun _ => rfl)]
    exact hh.2.2.2

#print axioms Cell.check_shareEndpoint
#print axioms RetentionPiece.check_shareEndpoint
#print axioms SourceIntervalCoverage.check_map_preserving_bounds
end ForestUnimodality.MessageCells
