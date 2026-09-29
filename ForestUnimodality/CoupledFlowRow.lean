import ForestUnimodality.CoupledFlowSources
import ForestUnimodality.FullFlowSources
import ForestUnimodality.ExtendedFlowSources
import ForestUnimodality.FlowComparisonCertificate

namespace ForestUnimodality.CoupledFlow
open ExtendedFlowSources

structure Row where
  start : ℚ
  finish : ℚ
  lower : ℚ
  totalUpper : ℚ
  next : ℚ
  nextUpper : ℚ
  charge : ℚ
  coarse : ℚ
  preLower : ℚ
  VB : ℚ
  VK : ℚ
  kappa : ℚ
  qu : ℚ
  Vc : ℚ
  fine : ℚ
  preliminary : Source
  varSource : Source
  fullSource : FullSource
  complement : ComplementSource
  endpoint : Source
  integral : Source
  preliminaryCert : FlowComparisonCertificate.Certificate
  endpointCert : FlowComparisonCertificate.Certificate
  integralCert : FlowComparisonCertificate.Certificate
  startExp : ExpEnclosure.PowerCertificate
  startExpLo : ℚ
  startExpHi : ℚ
  finishExp : ExpEnclosure.PowerCertificate
  finishExpLo : ℚ
  finishExpHi : ℚ

def Row.DP (r : Row) (e : Environment) : ℚ := r.preliminary.D e.beta r.coarse
def Row.DE (r : Row) (e : Environment) : ℚ := r.endpoint.D e.beta r.fine
def Row.DI (r : Row) (e : Environment) : ℚ := r.integral.D e.beta r.fine
def Row.CP (r : Row) : ℚ := r.preliminary.C
def Row.CE (r : Row) : ℚ := r.endpoint.C
def Row.CI (r : Row) : ℚ := r.integral.C
def Row.drift (r : Row) : ℚ := r.Vc/4-(1-r.qu)*r.preLower

def Row.Geometry (r : Row) : Prop :=
  0≤r.start ∧ r.start≤r.finish ∧ 0≤r.lower ∧ 0≤r.next ∧ 0≤r.charge ∧
  0≤r.preLower ∧ 0≤r.VB ∧ 0≤r.VK ∧ 0≤r.kappa ∧ r.qu≤1

def Row.Domains (r : Row) (e : Environment) : Prop :=
  r.startExp.check (-r.start) r.startExpLo r.startExpHi=true ∧
  r.finishExp.check (-r.finish) r.finishExpLo r.finishExpHi=true ∧
  r.preliminary.domainCheck e.a e.b r.startExpHi r.finishExpLo=true ∧
  r.varSource.domainCheck e.a e.b r.startExpHi r.finishExpLo=true ∧
  r.endpoint.domainCheck e.a e.b r.startExpHi r.finishExpLo=true ∧
  r.integral.domainCheck e.a e.b r.startExpHi r.finishExpLo=true ∧
  r.fullSource.domainCheck e.a e.b r.finishExpLo=true ∧ e.b≤r.complement.cap

def Row.Comparisons (r : Row) (e : Environment) : Prop :=
  r.preliminaryCert.check r.lower (r.DP e) r.CP (r.finish-r.start)=true ∧
  r.endpointCert.check r.lower (r.DE e) r.CE (r.finish-r.start)=true ∧
  r.integralCert.check r.lower (r.DI e) r.CI (r.finish-r.start)=true ∧
  r.preLower≤max 0 (r.preliminaryCert.endBound r.lower) ∧
  r.next≤max 0 (r.endpointCert.endBound r.lower) ∧
  r.charge≤max 0 (r.integralCert.areaBound r.lower (r.finish-r.start))

def Row.Refinement (r : Row) (e : Environment) : Prop :=
  min (r.totalUpper+e.eta*(r.finish-r.start)) e.globalCap≤r.coarse ∧
  e.b*r.startExpHi/(1+e.b*r.startExpHi)≤r.qu ∧
  r.varSource.D e.beta r.coarse+r.varSource.C*r.qu≤r.VB ∧
  r.fullSource.bound e.gamma r.coarse≤r.VK ∧
  r.VB*r.VK≤r.kappa^2 ∧
  r.complement.bound e.beta r.coarse r.preLower≤r.Vc ∧
  min (min (r.totalUpper+r.kappa*(r.finish-r.start)) r.coarse)
    (r.totalUpper+max 0 r.drift*(r.finish-r.start))≤r.fine ∧
  min r.fine (r.totalUpper+r.drift*(r.finish-r.start))≤r.nextUpper

def Row.Accepts (r : Row) (e : Environment) : Prop :=
  r.Geometry ∧ r.Domains e ∧ r.Comparisons e ∧ r.Refinement e
instance (r : Row) (e : Environment) : Decidable (r.Accepts e) := by
  unfold Row.Accepts Row.Geometry Row.Domains Row.Comparisons Row.Refinement
  infer_instance
def Row.check (r : Row) (e : Environment) : Bool := decide (r.Accepts e)

theorem Row.scalar_bounds {r : Row} {e : Environment} (hc : r.check e=true) :
    (r.start:ℝ)≤r.finish ∧ (0:ℝ)≤r.CE ∧ (0:ℝ)≤r.CI ∧
    (r.next:ℝ)≤max 0 (PiecewiseFlowZeroSlope.endLower r.lower (r.DE e) r.CE (r.finish-r.start)) ∧
    (r.charge:ℝ)≤max 0 (PiecewiseFlowZeroSlope.integralLower r.lower (r.DI e) r.CI (r.finish-r.start)) := by
  have h : r.Accepts e := of_decide_eq_true hc
  rcases h.2.2.1 with ⟨_,he,hi,_,hn,hq⟩
  have he' := FlowComparisonCertificate.Certificate.clamped_sound he hn (le_refl _)
  have hi' := FlowComparisonCertificate.Certificate.clamped_sound hi (le_refl _) hq
  refine ⟨by exact_mod_cast h.1.2.1,r.endpoint.C_nonneg,r.integral.C_nonneg,?_,?_⟩
  · simpa only [Rat.cast_sub] using he'.1
  · simpa only [Rat.cast_sub] using hi'.2

#print axioms Row.scalar_bounds
end ForestUnimodality.CoupledFlow
