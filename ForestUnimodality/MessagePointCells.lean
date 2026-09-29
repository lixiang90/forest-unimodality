import ForestUnimodality.MessageSharedCells
import ForestUnimodality.BernsteinPoint

namespace ForestUnimodality.BernsteinCertificate
def pointOrIntervalCheck (p : RatPolynomial) (lo hi : ℚ) (c : Certificate) : Bool :=
  if lo = hi then pointCheck p lo c else intervalCheck p lo hi c

theorem intervalCheck_of_pointOrIntervalCheck {p : RatPolynomial} {lo hi : ℚ} {c : Certificate}
    (h : pointOrIntervalCheck p lo hi c = true) : intervalCheck p lo hi c = true := by
  unfold pointOrIntervalCheck at h
  split_ifs at h with he
  · subst hi
    exact intervalCheck_of_pointCheck h
  · exact h
end ForestUnimodality.BernsteinCertificate

namespace ForestUnimodality.MessagePolynomialEnvelope
open ParametricQuadratic BernsteinCertificate

def Certificate.pointEndpointCheck (c : Certificate) (P : Parameters)
    (Bbelow Babove : Bounds) (Q : ParentPrices) (lo hi : ℚ) : Bool :=
  pointOrIntervalCheck (negativeQuad P Bbelow Q).A lo hi c.negative.leading &&
  pointOrIntervalCheck (negativeQuad P Bbelow Q).C lo hi c.negative.endpoint &&
  pointOrIntervalCheck (if c.negative.useSlope then (negativeQuad P Bbelow Q).B
    else (negativeQuad P Bbelow Q).discriminantMargin) lo hi c.negative.last &&
  pointOrIntervalCheck ((middleQuad P Bbelow Q).A + (middleQuad P Bbelow Q).B +
    (middleQuad P Bbelow Q).C) lo hi c.middle.right &&
  pointOrIntervalCheck (c.middle.branch.polynomial (middleQuad P Bbelow Q)) lo hi c.middle.last &&
  pointOrIntervalCheck (positiveQuad P Babove Q).A lo hi c.positive.leading &&
  pointOrIntervalCheck (positiveQuad P Babove Q).C lo hi c.positive.endpoint &&
  pointOrIntervalCheck (if c.positive.useSlope then (positiveQuad P Babove Q).B
    else (positiveQuad P Babove Q).discriminantMargin) lo hi c.positive.last

theorem Certificate.check_pointEndpoint {c : Certificate} {P : Parameters}
    {Bbelow Babove : Bounds} {Q : ParentPrices} {lo hi : ℚ}
    (h : c.pointEndpointCheck P Bbelow Babove Q lo hi = true) :
    c.shareEndpoint.check P Bbelow Babove Q lo hi = true := by
  apply Certificate.check_shareEndpoint
  simp only [Certificate.pointEndpointCheck, Bool.and_eq_true_iff, and_assoc] at h
  rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
  simp only [Certificate.sharedEndpointCheck, RayCertificate.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨intervalCheck_of_pointOrIntervalCheck h0, intervalCheck_of_pointOrIntervalCheck h1,
    intervalCheck_of_pointOrIntervalCheck h2, intervalCheck_of_pointOrIntervalCheck h3,
    intervalCheck_of_pointOrIntervalCheck h4, intervalCheck_of_pointOrIntervalCheck h5,
    intervalCheck_of_pointOrIntervalCheck h6, intervalCheck_of_pointOrIntervalCheck h7⟩
end ForestUnimodality.MessagePolynomialEnvelope

namespace ForestUnimodality.MessagePriceSpline


def ParentBranchCertificate.pointEndpointCheck (w : ParentBranchCertificate) (c : Segment)
    (P : MessagePolynomialEnvelope.Parameters) (Bbelow Babove : MessagePolynomialEnvelope.Bounds)
    (rl rh cap : ℚ) (moving : Bool) : Bool :=
  if c.lo ≤ c.parentUpper cap ∧ c.branchLeft rl cap moving ≤ c.branchRight rh moving then
    w.lower.pointEndpointCheck P Bbelow Babove
      (c.parentPolynomials (c.parentA moving) (Segment.parentB moving))
      (c.branchLeft rl cap moving) (c.branchRight rh moving) &&
    w.upper.pointEndpointCheck P Bbelow Babove (c.parentPolynomials (c.parentUpper cap) 0)
      (c.branchLeft rl cap moving) (c.branchRight rh moving)
  else true

theorem ParentBranchCertificate.check_pointEndpoint {w : ParentBranchCertificate} {c : Segment}
    {P : MessagePolynomialEnvelope.Parameters} {Bbelow Babove : MessagePolynomialEnvelope.Bounds}
    {rl rh cap : ℚ} {moving : Bool}
    (h : w.pointEndpointCheck c P Bbelow Babove rl rh cap moving = true) :
    w.shareEndpoint.check c P Bbelow Babove rl rh cap moving = true := by
  unfold ParentBranchCertificate.pointEndpointCheck at h
  unfold ParentBranchCertificate.check
  split_ifs with ha
  · rw [if_pos ha] at h
    have hh := Bool.and_eq_true_iff.mp h
    exact Bool.and_eq_true_iff.mpr
      ⟨MessagePolynomialEnvelope.Certificate.check_pointEndpoint hh.1,
       MessagePolynomialEnvelope.Certificate.check_pointEndpoint hh.2⟩
  · rfl


def ParentSegmentCertificate.pointEndpointCheck (w : ParentSegmentCertificate) (c : Segment)
    (P : MessagePolynomialEnvelope.Parameters) (Bbelow Babove : MessagePolynomialEnvelope.Bounds)
    (rl rh cap : ℚ) : Bool :=
  w.fixed.pointEndpointCheck c P Bbelow Babove rl rh cap false &&
    w.moving.pointEndpointCheck c P Bbelow Babove rl rh cap true

theorem ParentSegmentCertificate.check_pointEndpoint {w : ParentSegmentCertificate} {c : Segment}
    {P : MessagePolynomialEnvelope.Parameters} {Bbelow Babove : MessagePolynomialEnvelope.Bounds}
    {rl rh cap : ℚ}
    (h : w.pointEndpointCheck c P Bbelow Babove rl rh cap = true) :
    w.shareEndpoint.check c P Bbelow Babove rl rh cap = true := by
  have hh := Bool.and_eq_true_iff.mp h
  exact Bool.and_eq_true_iff.mpr
    ⟨ParentBranchCertificate.check_pointEndpoint hh.1,
     ParentBranchCertificate.check_pointEndpoint hh.2⟩

end ForestUnimodality.MessagePriceSpline



namespace ForestUnimodality.MessageCells
open MessagePriceSpline



def RetentionPiece.pointEndpointCheck (w : RetentionPiece) (P : Parameters)
    (D : Domain) (c : CellBounds) : Bool :=
  decide (w.parents.map ParentEntry.segment = P.pieces) &&
    w.parents.all (fun e => e.certificate.pointEndpointCheck e.segment (polynomialParameters P)
      (c.envelopeBounds D w.second true) (c.envelopeBounds D w.second false)
      w.lo w.hi (c.parentCap D))

theorem RetentionPiece.check_pointEndpoint {w : RetentionPiece} {P : Parameters}
    {D : Domain} {c : CellBounds} (h : w.pointEndpointCheck P D c = true) :
    w.shareEndpoint.check P D c = true := by
  have hh : w.parents.map ParentEntry.segment = P.pieces ∧
      w.parents.all (fun e => e.certificate.pointEndpointCheck e.segment (polynomialParameters P)
        (c.envelopeBounds D w.second true) (c.envelopeBounds D w.second false)
        w.lo w.hi (c.parentCap D)) = true := by
    simpa only [RetentionPiece.pointEndpointCheck, Bool.and_eq_true_iff, decide_eq_true_eq] using h
  simp only [RetentionPiece.check, Bool.and_eq_true_iff, decide_eq_true_eq]
  constructor
  · simpa only [RetentionPiece.shareEndpoint, List.map_map, Function.comp_def,
      ParentEntry.shareEndpoint] using hh.1
  · apply List.all_eq_true.mpr
    intro e he
    obtain ⟨original, ho, rfl⟩ := List.mem_map.mp he
    exact ParentSegmentCertificate.check_pointEndpoint ((List.all_eq_true.mp hh.2) original ho)


def Cell.pointEndpointCheck (c : Cell) (P : Parameters) (D : Domain) : Bool :=
  c.bounds.check P D && decide (c.bounds.base.retentionLower D < 1) &&
    c.pieces.all (fun w => w.pointEndpointCheck P D c.bounds) &&
    SourceIntervalCoverage.check RetentionPiece.lo RetentionPiece.hi
      (c.bounds.base.retentionLower D) 1 c.pieces

theorem Cell.check_pointEndpoint {c : Cell} {P : Parameters} {D : Domain}
    (h : c.pointEndpointCheck P D = true) : c.shareEndpoint.check P D = true := by
  have hh : c.bounds.check P D = true ∧ c.bounds.base.retentionLower D < 1 ∧
      c.pieces.all (fun w => w.pointEndpointCheck P D c.bounds) = true ∧
      SourceIntervalCoverage.check RetentionPiece.lo RetentionPiece.hi
        (c.bounds.base.retentionLower D) 1 c.pieces = true := by
    simpa only [Cell.pointEndpointCheck, Bool.and_eq_true_iff, decide_eq_true_eq, and_assoc] using h
  simp only [Cell.check, Cell.shareEndpoint, Bool.and_eq_true_iff, decide_eq_true_eq, and_assoc]
  refine ⟨hh.1, hh.2.1, ?_, ?_⟩
  · apply List.all_eq_true.mpr
    intro w hw
    obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hw
    exact RetentionPiece.check_pointEndpoint ((List.all_eq_true.mp hh.2.2.1) original ho)
  · rw [SourceIntervalCoverage.check_map_preserving_bounds RetentionPiece.shareEndpoint
      RetentionPiece.lo RetentionPiece.hi RetentionPiece.lo RetentionPiece.hi
      (fun _ => rfl) (fun _ => rfl)]
    exact hh.2.2.2

#print axioms Cell.check_pointEndpoint
#print axioms RetentionPiece.check_pointEndpoint

end ForestUnimodality.MessageCells
