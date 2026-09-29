import ForestUnimodality.CoupledFlowRow

/-! Equal comparison certificates need only one kernel reduction. The
geometry, refinement and each requested scalar bound are still checked. -/
namespace ForestUnimodality.CoupledFlow

def Row.SharedDomains (r : Row) (e : Environment) : Prop :=
  r.startExp.check (-r.start) r.startExpLo r.startExpHi=true ∧
  r.finishExp.check (-r.finish) r.finishExpLo r.finishExpHi=true ∧
  r.preliminary.domainCheck e.a e.b r.startExpHi r.finishExpLo=true ∧
  r.varSource.domainCheck e.a e.b r.startExpHi r.finishExpLo=true ∧
  r.endpoint.domainCheck e.a e.b r.startExpHi r.finishExpLo=true ∧
  r.fullSource.domainCheck e.a e.b r.finishExpLo=true ∧ e.b≤r.complement.cap

def Row.SharedComparisons (r : Row) (e : Environment) : Prop :=
  r.preliminaryCert.check r.lower (r.DP e) r.CP (r.finish-r.start)=true ∧
  r.endpointCert.check r.lower (r.DE e) r.CE (r.finish-r.start)=true ∧
  r.preLower≤max 0 (r.preliminaryCert.endBound r.lower) ∧
  r.next≤max 0 (r.endpointCert.endBound r.lower) ∧
  r.charge≤max 0 (r.endpointCert.areaBound r.lower (r.finish-r.start))

def Row.SharedAccepts (r : Row) (e : Environment) : Prop :=
  r.Geometry ∧ r.SharedDomains e ∧ r.SharedComparisons e ∧ r.Refinement e

instance (r : Row) (e : Environment) : Decidable (r.SharedAccepts e) := by
  unfold Row.SharedAccepts Row.Geometry Row.SharedDomains Row.SharedComparisons Row.Refinement
  infer_instance

def Row.sharedCheck (r : Row) (e : Environment) : Bool := decide (r.SharedAccepts e)

theorem Row.check_of_shared (r : Row) {e : Environment}
    (hs : r.integral=r.endpoint) (hc : r.integralCert=r.endpointCert)
    (h : r.sharedCheck e=true) : r.check e=true := by
  have hh : r.SharedAccepts e := of_decide_eq_true h
  rcases hh with ⟨hg,hd,hcmp,hf⟩
  rcases hd with ⟨hst,hfin,hpre,hvar,hend,hfull,hcomp⟩
  rcases hcmp with ⟨hp,he,hpb,hn,ha⟩
  apply decide_eq_true
  refine ⟨hg,⟨hst,hfin,hpre,hvar,hend,?_,hfull,hcomp⟩,
    ⟨hp,he,?_,hpb,hn,?_⟩,hf⟩
  · simpa only [hs] using hend
  · simpa only [Row.DI,Row.CI,Row.DE,Row.CE,hs,hc] using he
  · simpa only [hc] using ha

def Row.SingleDomains (r : Row) (e : Environment) : Prop :=
  r.startExp.check (-r.start) r.startExpLo r.startExpHi=true ∧
  r.finishExp.check (-r.finish) r.finishExpLo r.finishExpHi=true ∧
  r.varSource.domainCheck e.a e.b r.startExpHi r.finishExpLo=true ∧
  r.endpoint.domainCheck e.a e.b r.startExpHi r.finishExpLo=true ∧
  r.fullSource.domainCheck e.a e.b r.finishExpLo=true ∧ e.b≤r.complement.cap

def Row.SingleComparisons (r : Row) (e : Environment) : Prop :=
  r.endpointCert.check r.lower (r.DE e) r.CE (r.finish-r.start)=true ∧
  r.preLower≤max 0 (r.endpointCert.endBound r.lower) ∧
  r.next≤max 0 (r.endpointCert.endBound r.lower) ∧
  r.charge≤max 0 (r.endpointCert.areaBound r.lower (r.finish-r.start))

def Row.SingleAccepts (r : Row) (e : Environment) : Prop :=
  r.Geometry ∧ r.SingleDomains e ∧ r.SingleComparisons e ∧ r.Refinement e

instance (r : Row) (e : Environment) : Decidable (r.SingleAccepts e) := by
  unfold Row.SingleAccepts Row.Geometry Row.SingleDomains Row.SingleComparisons Row.Refinement
  infer_instance

def Row.singleCheck (r : Row) (e : Environment) : Bool := decide (r.SingleAccepts e)

theorem Row.check_of_single (r : Row) {e : Environment}
    (hs : r.integral=r.endpoint) (hc : r.integralCert=r.endpointCert)
    (hps : r.preliminary=r.endpoint) (hpc : r.preliminaryCert=r.endpointCert)
    (hD : r.DP e=r.DE e) (h : r.singleCheck e=true) : r.check e=true := by
  apply r.check_of_shared hs hc
  have hh : r.SingleAccepts e := of_decide_eq_true h
  rcases hh with ⟨hg,hd,hcmp,hf⟩
  rcases hd with ⟨hst,hfin,hvar,hend,hfull,hcomp⟩
  rcases hcmp with ⟨he,hpb,hn,ha⟩
  apply decide_eq_true
  refine ⟨hg,⟨hst,hfin,?_,hvar,hend,hfull,hcomp⟩,⟨?_,he,?_,hn,ha⟩,hf⟩
  · simpa only [hps] using hend
  · simpa only [hpc,hD,Row.CP,Row.CE,hps] using he
  · simpa only [hpc] using hpb

#print axioms Row.check_of_shared
#print axioms Row.check_of_single
end ForestUnimodality.CoupledFlow
