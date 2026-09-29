import ForestUnimodality.LowActivityFlowSources
import ForestUnimodality.FlowComparisonCertificate

namespace ForestUnimodality.LowActivityFlow
open LowActivityFlowSources

structure Row where
  start : ℚ
  finish : ℚ
  lower : ℚ
  next : ℚ
  charge : ℚ
  endpoint : Source
  integral : Source
  endpointCert : FlowComparisonCertificate.Certificate
  integralCert : FlowComparisonCertificate.Certificate
  startExp : ExpEnclosure.PowerCertificate
  startExpLo : ℚ
  startExpHi : ℚ

def Row.DE (r : Row) (beta : ℚ) : ℚ := A r.endpoint*beta
def Row.DI (r : Row) (beta : ℚ) : ℚ := A r.integral*beta
def Row.CE (r : Row) : ℚ := C r.endpoint
def Row.CI (r : Row) : ℚ := C r.integral

def Row.Accepts (r : Row) (b beta : ℚ) : Prop :=
  0≤r.start ∧ r.start≤r.finish ∧ 0≤r.lower ∧ 0≤r.next ∧ 0≤r.charge ∧
  b≤b0 r.endpoint ∧ b≤b0 r.integral ∧
  r.startExp.check (-r.start) r.startExpLo r.startExpHi=true ∧
  (r.endpoint=0 ∨ b*r.startExpHi≤b1 r.endpoint) ∧
  (r.integral=0 ∨ b*r.startExpHi≤b1 r.integral) ∧
  r.endpointCert.check r.lower (r.DE beta) r.CE (r.finish-r.start)=true ∧
  r.integralCert.check r.lower (r.DI beta) r.CI (r.finish-r.start)=true ∧
  r.next≤max 0 (r.endpointCert.endBound r.lower) ∧
  r.charge≤max 0 (r.integralCert.areaBound r.lower (r.finish-r.start))

instance (r : Row) (b beta : ℚ) : Decidable (r.Accepts b beta) := by
  unfold Row.Accepts
  infer_instance

def Row.check (r : Row) (b beta : ℚ) : Bool := decide (r.Accepts b beta)

theorem Row.scalar_bounds {r : Row} {b beta : ℚ} (hc : r.check b beta=true) :
    (r.start:ℝ)≤r.finish ∧ (0:ℝ)≤r.CE ∧ (0:ℝ)≤r.CI ∧
    (r.next:ℝ)≤max 0 (PiecewiseFlowZeroSlope.endLower r.lower (r.DE beta) r.CE (r.finish-r.start)) ∧
    (r.charge:ℝ)≤max 0 (PiecewiseFlowZeroSlope.integralLower r.lower (r.DI beta) r.CI (r.finish-r.start)) := by
  have h : r.Accepts b beta := of_decide_eq_true hc
  rcases h with ⟨_,horder,_,_,_,_,_,_,_,_,he,hi,hn,hq⟩
  have he' := FlowComparisonCertificate.Certificate.clamped_sound he hn (le_refl _)
  have hi' := FlowComparisonCertificate.Certificate.clamped_sound hi (le_refl _) hq
  refine ⟨by exact_mod_cast horder,(C_pos r.endpoint).le,(C_pos r.integral).le,?_,?_⟩
  · simpa only [Rat.cast_sub] using he'.1
  · simpa only [Rat.cast_sub] using hi'.2

variable {V : Type*} [DecidableEq V]

theorem Row.variance_bounds {r : Row} {b beta : ℚ} (hc : r.check b beta=true)
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V)) {z m t : ℝ}
    (hz : 0<z) (hzb : z≤(b:ℝ)) (hcard : (B.card:ℝ)≤m*(beta:ℝ))
    (ht : t∈Set.Icc (r.start:ℝ) (r.finish:ℝ)) :
    (FixedIndependentTilt.markedVariance G S B z t≤m*(r.DE beta:ℝ)+
      (r.CE:ℝ)*FixedIndependentTilt.markedMean G S B z t) ∧
    (FixedIndependentTilt.markedVariance G S B z t≤m*(r.DI beta:ℝ)+
      (r.CI:ℝ)*FixedIndependentTilt.markedMean G S B z t) := by
  have h : r.Accepts b beta := of_decide_eq_true hc
  rcases h with ⟨hs,_,_,_,_,hbe,hbi,hexp,hme,hmi,_,_,_,_⟩
  have hexp' := (r.startExp.check_sound hexp).2
  push_cast at hexp'
  have hb : (0:ℝ)<b := hz.trans_le hzb
  have hstart : (0:ℝ)≤r.start := by exact_mod_cast hs
  have hmarked (i : Source) (hcap : i=0 ∨ b*r.startExpHi≤b1 i) :
      i≠0 → z*Real.exp (-(r.start:ℝ))≤(b1 i:ℝ) := by
    intro hi
    rcases hcap with he|hc
    · exact (hi he).elim
    · have hcapR : (b:ℝ)*r.startExpHi≤b1 i := by exact_mod_cast hc
      exact (mul_le_mul hzb hexp' (Real.exp_pos _).le hb.le).trans hcapR
  have he := LowActivityFlowSources.actual_variance r.endpoint G hG S B hBS hB hz hstart ht.1
    (hzb.trans (by exact_mod_cast hbe)) (hmarked _ hme) hcard
  have hi := LowActivityFlowSources.actual_variance r.integral G hG S B hBS hB hz hstart ht.1
    (hzb.trans (by exact_mod_cast hbi)) (hmarked _ hmi) hcard
  simpa only [Row.DE,Row.DI,Row.CE,Row.CI,Rat.cast_mul] using And.intro he hi

#print axioms Row.scalar_bounds
#print axioms Row.variance_bounds
end ForestUnimodality.LowActivityFlow
