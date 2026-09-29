import ForestUnimodality.FlowSourceDomainCheck
import ForestUnimodality.LegacyMarkedSourceLibrary

namespace ForestUnimodality.ExtendedFlowSources
open Set

inductive Source where
  | base : FlowVarianceSources.Source→Source
  | legacy : Fin 10→Source
  deriving DecidableEq
def Source.D : Source→ℚ→ℚ→ℚ
  | .base s,beta,U => s.D beta U
  | .legacy i,_,U => (LegacyMarkedSourceLibrary.parameters i).A*U
def Source.C : Source→ℚ
  | .base s => s.C
  | .legacy i => (LegacyMarkedSourceLibrary.parameters i).C
def Source.needsMean : Source→Bool
  | .base s => s.needsMean
  | .legacy _ => true
def Source.Covers : Source→ℝ→ℝ→ℝ→ℝ→Prop
  | .base s,a,b,start,finish => s.Covers a b start finish
  | .legacy i,a,b,_,finish => (LegacyMarkedSourceLibrary.lower i:ℝ)≤a*Real.exp (-finish) ∧
      b≤(LegacyMarkedSourceLibrary.upper i:ℝ)
def Source.DomainAccepts : Source→ℚ→ℚ→ℚ→ℚ→Prop
  | .base s,a,b,shi,flo => s.DomainAccepts a b shi flo
  | .legacy i,a,b,_,flo => LegacyMarkedSourceLibrary.lower i≤a*flo ∧ b≤LegacyMarkedSourceLibrary.upper i
instance (s : Source) (a b shi flo : ℚ) : Decidable (s.DomainAccepts a b shi flo) := by
  cases s <;> unfold Source.DomainAccepts <;> infer_instance
def Source.domainCheck (s : Source) (a b shi flo : ℚ) : Bool := decide (s.DomainAccepts a b shi flo)

theorem Source.C_nonneg (s : Source) : (0:ℝ)≤s.C := by
  cases s with
  | base s => exact s.C_nonneg
  | legacy i => exact (LegacyMarkedSourceLibrary.coefficients_nonneg i).2

theorem Source.domain_sound {s : Source} {a b shi flo : ℚ} {start finish : ℝ}
    (hc : s.domainCheck a b shi flo=true) (ha : (0:ℝ)≤a) (hb : (0:ℝ)≤b)
    (hs : Real.exp (-start)≤(shi:ℝ)) (hf : (flo:ℝ)≤Real.exp (-finish)) :
    s.Covers a b start finish := by
  have h : s.DomainAccepts a b shi flo := of_decide_eq_true hc
  cases s with
  | base s => exact s.domain_sound (by exact decide_eq_true h) ha hb hs hf
  | legacy i =>
    refine ⟨?_,by exact_mod_cast h.2⟩
    have hh : (LegacyMarkedSourceLibrary.lower i:ℝ)≤(a:ℝ)*flo := by exact_mod_cast h.1
    exact hh.trans (mul_le_mul_of_nonneg_left hf ha)

variable {V : Type*} [DecidableEq V]
theorem Source.actual_variance (s : Source) {beta U : ℚ}
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V)) {z a b start finish m : ℝ}
    (ha : 0<a) (hzlo : a≤z) (hzhi : z≤b) (hstart : 0≤start)
    (hcover : s.Covers a b start finish) (hcard : (B.card:ℝ)≤m*(beta:ℝ))
    (hmu : s.needsMean=true → ∀t∈Icc start finish, FixedIndependentTilt.totalMean G S B z t≤m*(U:ℝ)) :
    ∀t∈Icc start finish, FixedIndependentTilt.markedVariance G S B z t≤
      m*(s.D beta U:ℝ)+(s.C:ℝ)*FixedIndependentTilt.markedMean G S B z t := by
  cases s with
  | base s => exact s.actual_variance G hG S B hBS hB ha hzlo hzhi hstart hcover hcard hmu
  | legacy i =>
    have hh := LegacyMarkedSourceLibrary.variance_on_step i G hG S B hB ha hzlo hzhi hstart
      hcover.1 hcover.2 (hmu rfl)
    simpa only [Source.D,Source.C,Rat.cast_mul] using hh

theorem variance_cap {s : Source} {beta U qu v : ℚ}
    (G : SimpleGraph V) (S B : Finset V) {z t m : ℝ} (hm : 0≤m)
    (hvar : FixedIndependentTilt.markedVariance G S B z t≤m*(s.D beta U:ℝ)+
      (s.C:ℝ)*FixedIndependentTilt.markedMean G S B z t)
    (hw : FixedIndependentTilt.markedMean G S B z t≤m*(qu:ℝ))
    (hcap : s.D beta U+s.C*qu≤v) :
    FixedIndependentTilt.markedVariance G S B z t≤m*(v:ℝ) := by
  have h₁ := mul_le_mul_of_nonneg_left hw s.C_nonneg
  have hr : (s.D beta U:ℝ)+(s.C:ℝ)*qu≤v := by exact_mod_cast hcap
  have h₂ := mul_le_mul_of_nonneg_left hr hm
  nlinarith

#print axioms Source.C_nonneg
#print axioms Source.domain_sound
#print axioms Source.actual_variance
#print axioms variance_cap
end ForestUnimodality.ExtendedFlowSources
