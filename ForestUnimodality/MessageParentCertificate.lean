import ForestUnimodality.MessageParentBranches

/-! Finite certificates for the two clipped endpoints of a common parent
price segment. Each endpoint keeps all four prices at the same parent.
The split includes every retention value, including point intervals. -/
namespace ForestUnimodality.MessagePriceSpline
open MessagePolynomialEnvelope

structure ParentBranchCertificate where
  lower : Certificate
  upper : Certificate

def ParentBranchCertificate.check (w : ParentBranchCertificate) (c : Segment)
    (P : MessagePolynomialEnvelope.Parameters) (Bbelow Babove : Bounds)
    (rl rh cap : ℚ) (moving : Bool) : Bool :=
  if c.lo≤c.parentUpper cap ∧ c.branchLeft rl cap moving≤c.branchRight rh moving then
    w.lower.check P Bbelow Babove
      (c.parentPolynomials (c.parentA moving) (Segment.parentB moving))
      (c.branchLeft rl cap moving) (c.branchRight rh moving) &&
    w.upper.check P Bbelow Babove (c.parentPolynomials (c.parentUpper cap) 0)
      (c.branchLeft rl cap moving) (c.branchRight rh moving)
  else true

structure ParentSegmentCertificate where
  fixed : ParentBranchCertificate
  moving : ParentBranchCertificate

def ParentSegmentCertificate.check (w : ParentSegmentCertificate) (c : Segment)
    (P : MessagePolynomialEnvelope.Parameters) (Bbelow Babove : Bounds)
    (rl rh cap : ℚ) : Bool :=
  w.fixed.check c P Bbelow Babove rl rh cap false &&
    w.moving.check c P Bbelow Babove rl rh cap true

noncomputable def signedMarkedEnvelope (P : MessageSourceParameters)
    (Bbelow Babove : Bounds) (r z : ℝ) (c : Segment) (parent : ℝ) : ℝ :=
  messageSourceMarkedEnvelope P (if z≤1 then Bbelow.toReal else Babove.toReal) r z
    (c.atReal parent).u (c.atReal parent).v (c.atReal parent).s (c.atReal parent).tau

theorem signedEnvelope_eq_marked (c : Segment) (a b : ℚ) (r z : ℝ)
    (P : MessagePolynomialEnvelope.Parameters) (Bbelow Babove : Bounds)
    (A : MessageSourceParameters)
    (hCJ : A.CJ=(P.CJ:ℝ)) (hCmu : A.Cmu=(P.Cmu:ℝ))
    (hw : A.w=(P.w:ℝ)) (ht : A.t=(P.t:ℝ)) :
    signedEnvelope P Bbelow Babove (c.parentPolynomials a b) r z =
      signedMarkedEnvelope A Bbelow Babove r z c ((a:ℝ)+(b:ℝ)*r) := by
  unfold signedEnvelope signedMarkedEnvelope
  split_ifs <;> exact c.polynomial_envelope_eq_marked a b r z P _ A hCJ hCmu hw ht

theorem ParentBranchCertificate.check_sound {w : ParentBranchCertificate} {c : Segment}
    {P : MessagePolynomialEnvelope.Parameters} {Bbelow Babove : Bounds}
    {rl rh cap : ℚ} {moving : Bool}
    (hc : w.check c P Bbelow Babove rl rh cap moving=true)
    (hlo : c.lo≤c.parentUpper cap) {r z : ℝ}
    (hr : r∈Set.Icc (c.branchLeft rl cap moving:ℝ) (c.branchRight rh moving:ℝ)) :
    0≤signedEnvelope P Bbelow Babove
      (c.parentPolynomials (c.parentA moving) (Segment.parentB moving)) r z ∧
    0≤signedEnvelope P Bbelow Babove (c.parentPolynomials (c.parentUpper cap) 0) r z := by
  have hord : c.branchLeft rl cap moving≤c.branchRight rh moving := by
    exact_mod_cast hr.1.trans hr.2
  have hh := hc
  have hactive : c.lo≤c.parentUpper cap ∧
      c.branchLeft rl cap moving≤c.branchRight rh moving := ⟨hlo,hord⟩
  simp only [ParentBranchCertificate.check,if_pos hactive,
    Bool.and_eq_true_iff] at hh
  exact ⟨Certificate.check_sound hh.1 hr,Certificate.check_sound hh.2 hr⟩

/-- Both actual clipped endpoints have nonnegative signed envelopes. The
checker, rather than an unproved positivity hypothesis, supplies the result. -/
theorem ParentSegmentCertificate.check_sound {w : ParentSegmentCertificate} {c : Segment}
    {P : MessagePolynomialEnvelope.Parameters} {Bbelow Babove : Bounds}
    {rl rh cap : ℚ} (hc : w.check c P Bbelow Babove rl rh cap=true)
    (A : MessageSourceParameters)
    (hCJ : A.CJ=(P.CJ:ℝ)) (hCmu : A.Cmu=(P.Cmu:ℝ))
    (hw : A.w=(P.w:ℝ)) (ht : A.t=(P.t:ℝ))
    {r z : ℝ} (hr : r∈Set.Icc (rl:ℝ) (rh:ℝ))
    (hinter : max (c.lo:ℝ) (1-r)≤min (c.hi:ℝ) (cap:ℝ)) :
    0≤signedMarkedEnvelope A Bbelow Babove r z c (max (c.lo:ℝ) (1-r)) ∧
    0≤signedMarkedEnvelope A Bbelow Babove r z c (min (c.hi:ℝ) (cap:ℝ)) := by
  obtain ⟨moving,hr',hp,hlo⟩ := c.parent_branch_cover rl rh cap hr hinter
  have hchecks : w.fixed.check c P Bbelow Babove rl rh cap false=true ∧
      w.moving.check c P Bbelow Babove rl rh cap true=true := by
    simpa only [ParentSegmentCertificate.check,Bool.and_eq_true_iff] using hc
  have hpos : 0≤signedEnvelope P Bbelow Babove
      (c.parentPolynomials (c.parentA moving) (Segment.parentB moving)) r z ∧
      0≤signedEnvelope P Bbelow Babove (c.parentPolynomials (c.parentUpper cap) 0) r z := by
    cases moving with
    | false => exact ParentBranchCertificate.check_sound hchecks.1 hlo hr'
    | true => exact ParentBranchCertificate.check_sound hchecks.2 hlo hr'
  rw [signedEnvelope_eq_marked c _ _ r z P Bbelow Babove A hCJ hCmu hw ht,hp] at hpos
  rw [signedEnvelope_eq_marked c _ _ r z P Bbelow Babove A hCJ hCmu hw ht] at hpos
  simpa only [Rat.cast_zero,zero_mul,add_zero,Segment.parentUpper,Rat.cast_min] using hpos

#print axioms ParentBranchCertificate.check_sound
#print axioms ParentSegmentCertificate.check_sound
end ForestUnimodality.MessagePriceSpline
