import ForestUnimodality.MessageParentBranches

/-! The negative and middle response quadratics have the same value at zero.
An identical endpoint witness therefore needs only one Bernstein check. -/
namespace ForestUnimodality.MessagePolynomialEnvelope
open ParametricQuadratic BernsteinCertificate

def Certificate.sharedEndpointCheck (c : Certificate) (P : Parameters)
    (Bbelow Babove : Bounds) (Q : ParentPrices) (lo hi : ℚ) : Bool :=
  c.negative.check (negativeQuad P Bbelow Q) lo hi &&
    intervalCheck ((middleQuad P Bbelow Q).A + (middleQuad P Bbelow Q).B +
      (middleQuad P Bbelow Q).C) lo hi c.middle.right &&
    intervalCheck (c.middle.branch.polynomial (middleQuad P Bbelow Q)) lo hi c.middle.last &&
    c.positive.check (positiveQuad P Babove Q) lo hi

theorem Certificate.check_of_shared_endpoint {c : Certificate} {P : Parameters}
    {Bbelow Babove : Bounds} {Q : ParentPrices} {lo hi : ℚ}
    (hsame : c.middle.left = c.negative.endpoint)
    (h : c.sharedEndpointCheck P Bbelow Babove Q lo hi = true) :
    c.check P Bbelow Babove Q lo hi = true := by
  have hh : c.negative.check (negativeQuad P Bbelow Q) lo hi = true ∧
      intervalCheck ((middleQuad P Bbelow Q).A + (middleQuad P Bbelow Q).B +
        (middleQuad P Bbelow Q).C) lo hi c.middle.right = true ∧
      intervalCheck (c.middle.branch.polynomial (middleQuad P Bbelow Q)) lo hi c.middle.last = true ∧
      c.positive.check (positiveQuad P Babove Q) lo hi = true := by
    simpa only [Certificate.sharedEndpointCheck, Bool.and_eq_true_iff, and_assoc] using h
  have hn : intervalCheck (negativeQuad P Bbelow Q).A lo hi c.negative.leading = true ∧
      intervalCheck (negativeQuad P Bbelow Q).C lo hi c.negative.endpoint = true ∧
      intervalCheck (if c.negative.useSlope then (negativeQuad P Bbelow Q).B
        else (negativeQuad P Bbelow Q).discriminantMargin) lo hi c.negative.last = true := by
    simpa only [RayCertificate.check, Bool.and_eq_true_iff, and_assoc] using hh.1
  have he : intervalCheck (middleQuad P Bbelow Q).C lo hi c.middle.left = true := by
    rw [hsame]
    exact hn.2.1
  have hm : c.middle.check (middleQuad P Bbelow Q) lo hi = true := by
    simpa only [UnitCertificate.check, Bool.and_eq_true_iff, and_assoc] using
      And.intro he (And.intro hh.2.1 hh.2.2.1)
  simpa only [Certificate.check, Bool.and_eq_true_iff, and_assoc] using
    And.intro hh.1 (And.intro hm hh.2.2.2)

#print axioms Certificate.check_of_shared_endpoint
end ForestUnimodality.MessagePolynomialEnvelope
