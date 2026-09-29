import ForestUnimodality.BasicFlowSourceCheck

namespace ForestUnimodality.FlowVarianceSources
open Set

def Source.DomainAccepts (s : Source) (a b startHi finishLo : ℚ) : Prop :=
  match s with
  | .marked i => (Stage99MarkedSourceLibrary.domain i).lower≤a*finishLo ∧
      b≤(Stage99MarkedSourceLibrary.domain i).b
  | _ => s.BasicAccepts b startHi
instance (s : Source) (a b startHi finishLo : ℚ) : Decidable (s.DomainAccepts a b startHi finishLo) := by
  cases s <;> unfold Source.DomainAccepts <;> infer_instance
def Source.domainCheck (s : Source) (a b startHi finishLo : ℚ) : Bool :=
  decide (s.DomainAccepts a b startHi finishLo)

theorem Source.domain_sound {s : Source} {a b startHi finishLo : ℚ} {start finish : ℝ}
    (hc : s.domainCheck a b startHi finishLo=true) (ha : (0:ℝ)≤a) (hb : (0:ℝ)≤b)
    (hs : Real.exp (-start)≤(startHi:ℝ)) (hf : (finishLo:ℝ)≤Real.exp (-finish)) :
    s.Covers a b start finish := by
  have h : s.DomainAccepts a b startHi finishLo := of_decide_eq_true hc
  cases s with
  | uniform i =>
    exact (Source.basic_sound (s:=.uniform i) (by exact decide_eq_true h) hb hs).2
  | support i =>
    exact (Source.basic_sound (s:=.support i) (by exact decide_eq_true h) hb hs).2
  | tilted i =>
    exact (Source.basic_sound (s:=.tilted i) (by exact decide_eq_true h) hb hs).2
  | marked i =>
    refine ⟨?_,by exact_mod_cast h.2⟩
    have hlo : ((Stage99MarkedSourceLibrary.domain i).lower:ℝ)≤(a:ℝ)*finishLo := by exact_mod_cast h.1
    exact hlo.trans (mul_le_mul_of_nonneg_left hf ha)

theorem logistic_upper {z t start : ℝ} {b expHi qu : ℚ}
    (hz : 0<z) (hzb : z≤(b:ℝ)) (ht : start≤t)
    (he : Real.exp (-start)≤(expHi:ℝ))
    (hq : b*expHi/(1+b*expHi)≤qu) : logisticTilt z t≤(qu:ℝ) := by
  have hb : (0:ℝ)<b := hz.trans_le hzb
  have he0 : (0:ℝ)≤expHi := (Real.exp_pos _).le.trans he
  have hprod := mul_le_mul hzb he (Real.exp_pos _).le hb.le
  have hfrac : logisticTilt z start≤((b:ℝ)*expHi)/(1+(b:ℝ)*expHi) := by
    unfold logisticTilt
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  exact ((logisticTilt_antitone hz ht).trans hfrac).trans (by exact_mod_cast hq)

variable {V : Type*} [DecidableEq V]
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

#print axioms Source.domain_sound
#print axioms logistic_upper
#print axioms variance_cap
end ForestUnimodality.FlowVarianceSources
