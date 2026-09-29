import ForestUnimodality.BasicFlowRow

/-! When endpoint and integral comparisons use the same affine source and
certificate, checking them once suffices for both conclusions. -/
namespace ForestUnimodality.BasicFlow

def Row.SharedAccepts (r : Row) (b beta : ℚ) : Prop :=
  0≤r.start ∧ r.start≤r.finish ∧ 0≤r.lower ∧ 0≤r.next ∧ 0≤r.charge ∧
  r.startExp.check (-r.start) r.startExpLo r.startExpHi=true ∧
  r.endpoint.basicCheck b r.startExpHi=true ∧
  r.endpointCert.check r.lower (r.DE beta) r.CE (r.finish-r.start)=true ∧
  r.next≤max 0 (r.endpointCert.endBound r.lower) ∧
  r.charge≤max 0 (r.endpointCert.areaBound r.lower (r.finish-r.start))

instance (r : Row) (b beta : ℚ) : Decidable (r.SharedAccepts b beta) := by
  unfold Row.SharedAccepts
  infer_instance

def Row.sharedCheck (r : Row) (b beta : ℚ) : Bool := decide (r.SharedAccepts b beta)

theorem Row.check_of_shared (r : Row) {b beta : ℚ}
    (hs : r.integral=r.endpoint) (hc : r.integralCert=r.endpointCert)
    (h : r.sharedCheck b beta=true) : r.check b beta=true := by
  have hh : r.SharedAccepts b beta := of_decide_eq_true h
  rcases hh with ⟨h0,h1,h2,h3,h4,he,hsource,hcert,hn,ha⟩
  apply decide_eq_true
  refine ⟨h0,h1,h2,h3,h4,he,hsource,?_,hcert,?_,hn,?_⟩
  · simpa only [hs] using hsource
  · simpa only [Row.DI,Row.CI,Row.DE,Row.CE,hs,hc] using hcert
  · simpa only [hc] using ha

#print axioms Row.check_of_shared
end ForestUnimodality.BasicFlow
