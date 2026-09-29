import ForestUnimodality.BasicFlowSourceCheck
import ForestUnimodality.FlowComparisonCertificate

namespace ForestUnimodality.BasicFlow
open FlowVarianceSources

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

def Row.DE (r : Row) (beta : ℚ) : ℚ := r.endpoint.D beta 0
def Row.DI (r : Row) (beta : ℚ) : ℚ := r.integral.D beta 0
def Row.CE (r : Row) : ℚ := r.endpoint.C
def Row.CI (r : Row) : ℚ := r.integral.C

def Row.Accepts (r : Row) (b beta : ℚ) : Prop :=
  0≤r.start ∧ r.start≤r.finish ∧ 0≤r.lower ∧ 0≤r.next ∧ 0≤r.charge ∧
  r.startExp.check (-r.start) r.startExpLo r.startExpHi=true ∧
  r.endpoint.basicCheck b r.startExpHi=true ∧ r.integral.basicCheck b r.startExpHi=true ∧
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
  rcases h with ⟨_,horder,_,_,_,_,_,_,he,hi,hn,hq⟩
  have he' := FlowComparisonCertificate.Certificate.clamped_sound he hn (le_refl _)
  have hi' := FlowComparisonCertificate.Certificate.clamped_sound hi (le_refl _) hq
  refine ⟨by exact_mod_cast horder,r.endpoint.C_nonneg,r.integral.C_nonneg,?_,?_⟩
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
  rcases h with ⟨hs,_,_,_,_,hexp,hse,hsi,_,_,_,_⟩
  have he := (r.startExp.check_sound hexp).2
  push_cast at he
  have hb : (0:ℝ)≤b := (hz.trans_le hzb).le
  have hsR : (0:ℝ)≤r.start := by exact_mod_cast hs
  have hec := Source.basic_sound (a:=z) (finish:=(r.finish:ℝ)) hse hb he
  have hic := Source.basic_sound (a:=z) (finish:=(r.finish:ℝ)) hsi hb he
  have hev := r.endpoint.actual_variance (U:=0) G hG S B hBS hB hz (le_refl z) hzb hsR hec.2 hcard
    (by intro hh; rw [hec.1] at hh; cases hh) t ht
  have hiv := r.integral.actual_variance (U:=0) G hG S B hBS hB hz (le_refl z) hzb hsR hic.2 hcard
    (by intro hh; rw [hic.1] at hh; cases hh) t ht
  exact ⟨hev,hiv⟩

#print axioms Row.scalar_bounds
#print axioms Row.variance_bounds
end ForestUnimodality.BasicFlow
