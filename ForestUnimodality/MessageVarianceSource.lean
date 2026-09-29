import ForestUnimodality.MessagePricedCapacity
import ForestUnimodality.MessageBlockingCapacity
import ForestUnimodality.MessageSourceDomain
import ForestUnimodality.SourceSelectionCertificate

/-! Soundness of message-priced stage-80 variance sources. The scalar
predicate is a continuous-domain obligation, not a sampled numeric flag.
The parent prices use one and the same actual parent message. -/
namespace ForestUnimodality
open Finset MarginalSelectionBound
variable {V : Type*} [DecidableEq V]

structure MessageSourceParameters where
  CJ : ℝ
  Cmu : ℝ
  w : ℝ
  t : ℝ
  u : ℝ → ℝ
  v : ℝ → ℝ
  s : ℝ → ℝ
  tau : ℝ → ℝ
  Dn : ℝ
  ell : ℝ

def MessageSourceParameters.Admissible (P : MessageSourceParameters) (b : ℝ) : Prop :=
  0≤P.w ∧ 0≤P.ell ∧ ∀ p∈Set.Icc 0 (b/(1+b)),
    0≤P.u p ∧ 0≤P.v p ∧ 0≤P.s p

noncomputable def sourceLogReference (lower p : ℝ) : ℝ :=
  Real.log p-2*Real.log (1-p)-Real.log lower

noncomputable def messageSourceCore (P : MessageSourceParameters)
    (lower b p r d : ℝ) : ℝ :=
  P.CJ*r*selectionFraction (b/(1+b)) (p*r)+P.Cmu*r-r*(1-p)*d^2+
  P.w*(d-1+r*sourcePhi lower b p)+P.t*(d-r)+
  (P.Dn-P.ell*sourceLogReference lower p)/p

noncomputable def messageSourceMarkedRow (P : MessageSourceParameters)
    (lower b p r d pu pv ps pt : ℝ) : ℝ :=
  messageSourceCore P lower b p r d+
  (P.u p*(1/(p*sourceLogCapacity b p))*(max 0 (1-d))^2-
    pu*sourceExactH p*(max 0 d)^2)+
  (P.v p*(1/(p*sourceLogCapacity b p))*(max 0 (d-1))^2-
    pv*sourceExactH p*(max 0 (-d))^2)+
  (P.s p*r*((1-d)^2/sourceOddsCapacity b (sourceLogCapacity b p))-
    (1-r)*ps*(1-p)*d^2)+
  (r*P.tau p*(d-1)+(1-r)*pt*d)

noncomputable def messageSourceScalarRow (P : MessageSourceParameters)
    (lower b p r d parentp : ℝ) : ℝ :=
  messageSourceMarkedRow P lower b p r d
    (P.u parentp) (P.v parentp) (P.s parentp) (P.tau parentp)

def MessageSourceRowValid (P : MessageSourceParameters) (lower b : ℝ) : Prop :=
  ∀ p r d parentp : ℝ, 0<p → p≤b/(1+b) →
    1/(1+b*(1-p))≤r → r≤1 →
    1-r≤parentp → parentp≤b*(1-p)/(1+b*(1-p)) →
    (p=b/(1+b) → d=1) →
    0≤messageSourceScalarRow P lower b p r d parentp

theorem messageSourceCore_mul (P : MessageSourceParameters)
    (lower b p pi d : ℝ) (hp : p≠0) :
    p*messageSourceCore P lower b p (pi/p) d =
      P.CJ*(pi*selectionFraction (b/(1+b)) pi)+P.Cmu*pi-pi*(1-p)*d^2+
      P.w*(p*((pi/p)*(1+sourcePhi lower b p)-1))+
      (P.t+P.w)*(p*d-pi)+P.Dn-P.ell*sourceLogReference lower p := by
  unfold messageSourceCore
  have hpr : p*(pi/p)=pi := by field_simp
  rw [hpr]
  field_simp
  ring

/-- At a root, the scalar row additionally subtracts the nonnegative prices
u(0),v(0). Thus it is stronger than the actual summed capacity row. The
blocking and signed-response parent terms vanish exactly at a root. -/
theorem SourceMessages.message_scalar_le_marked
    {G : SimpleGraph V} {S : Finset V} {activity : V→ℝ}
    {parent : V→Option V} {p d : V→ℝ}
    (h : SourceMessages G S activity (fun _=>1) parent p d)
    (hactivity : ∀ x∈S,0<activity x) (P : MessageSourceParameters)
    (hu0 : 0≤P.u 0) (hv0 : 0≤P.v 0) (lower b : ℝ) {x : V} (hx : x∈S) :
    messageSourceScalarRow P lower b (p x)
      (heterogeneousMarginal G S activity x/p x) (d x)
      (sourceParentMark p (parent x)) ≤
    messageSourceMarkedRow P lower b (p x)
      (heterogeneousMarginal G S activity x/p x) (d x)
      (sourceParentMark (fun y=>P.u (p y)) (parent x))
      (sourceParentMark (fun y=>P.v (p y)) (parent x))
      (sourceParentMark (fun y=>P.s (p y)) (parent x))
      (sourceParentMark (fun y=>P.tau (p y)) (parent x)) := by
  cases hh : parent x with
  | some y => rfl
  | none =>
      have hr : heterogeneousMarginal G S activity x/p x=1 := by
        rw [h.marginal x hx,hh]
        simp [sourceParentMass,(h.probability_pos hactivity hx).ne']
      have hH := (sourceExactH_pos (h.probability x hx).1 (h.probability x hx).2).le
      have hu := mul_nonneg (mul_nonneg hu0 hH) (sq_nonneg (max 0 (d x)))
      have hv := mul_nonneg (mul_nonneg hv0 hH) (sq_nonneg (max 0 (-d x)))
      simp only [messageSourceScalarRow,messageSourceMarkedRow,sourceParentMark,hr,
        sub_self,zero_mul,mul_zero,sub_zero,add_zero,one_mul]
      linarith

theorem SourceMessages.message_core_sum
    {G : SimpleGraph V} {S : Finset V} {activity : V→ℝ}
    {parent : V→Option V} {p d : V→ℝ}
    (h : SourceMessages G S activity (fun _=>1) parent p d)
    (hactivity : ∀ x∈S,0<activity x)
    (P : MessageSourceParameters) (lower b : ℝ) :
    (∑x∈S,p x*messageSourceCore P lower b (p x)
      (heterogeneousMarginal G S activity x/p x) (d x)) =
    P.CJ*(∑x∈S,heterogeneousMarginal G S activity x*
      selectionFraction (b/(1+b)) (heterogeneousMarginal G S activity x))+
    P.Cmu*(∑x∈S,heterogeneousMarginal G S activity x)-
    (∑x∈S,heterogeneousMarginal G S activity x*(1-p x)*d x^2)+
    P.w*sourcePhiBudget G S activity p lower b+
    (P.t+P.w)*((∑x∈S,p x*d x)-(∑x∈S,heterogeneousMarginal G S activity x))+
    P.Dn*(S.card:ℝ)-P.ell*(∑x∈S,sourceLogReference lower (p x)) := by
  simp only [sourcePhiBudget,mul_sum,←sum_sub_distrib,←sum_add_distrib]
  rw [show P.Dn*(S.card:ℝ)=∑_x∈S,P.Dn by simp; ring]
  rw [←sum_add_distrib,←sum_sub_distrib]
  apply sum_congr rfl
  intro x hx
  simpa only [mul_sub] using
    messageSourceCore_mul P lower b (p x) _ (d x) (h.probability_pos hactivity hx).ne'

/-- Summation soundness with the exact original message log mass retained.
No sign is imposed on Dn or either response multiplier. -/
theorem SourceMessages.message_variance_sum_bound
    {G : SimpleGraph V} {S : Finset V} {activity : V→ℝ}
    {parent : V→Option V} {p d : V→ℝ}
    (h : SourceMessages G S activity (fun _=>1) parent p d)
    {lower b : ℝ} (hlower : 0<lower)
    (hactivity : ∀ x∈S,0<activity x ∧ activity x≤b)
    (P : MessageSourceParameters) (hP : P.Admissible b)
    (hlo : P.w=0 ∨ ∀x∈S,lower≤activity x)
    (hmean : (∑x∈S,p x*d x)=∑x∈S,heterogeneousMarginal G S activity x)
    (hvalid : MessageSourceRowValid P lower b) :
    (∑x∈S,heterogeneousMarginal G S activity x*(1-p x)*d x^2) ≤
    P.CJ*(∑x∈S,heterogeneousMarginal G S activity x*
      selectionFraction (b/(1+b)) (heterogeneousMarginal G S activity x))+
    P.Cmu*(∑x∈S,heterogeneousMarginal G S activity x)+
    P.Dn*(S.card:ℝ)-P.ell*(∑x∈S,sourceLogReference lower (p x)) := by
  by_cases hS : S=∅
  · subst S; simp
  have hb : 0<b := by
    obtain ⟨x,hx⟩ := nonempty_iff_ne_empty.mpr hS
    exact (hactivity x hx).1.trans_le (hactivity x hx).2
  have hweight : ∀x∈S,0≤P.u (p x) ∧ 0≤P.v (p x) ∧ 0≤P.s (p x) :=
    fun x hx=>hP.2.2 _ ⟨(h.probability x hx).1,h.probability_le_bound hactivity hx⟩
  have hzero := hP.2.2 0 ⟨le_rfl,div_nonneg hb.le (by linarith)⟩
  have hrow : 0≤∑x∈S,p x*messageSourceMarkedRow P lower b (p x)
      (heterogeneousMarginal G S activity x/p x) (d x)
      (sourceParentMark (fun y=>P.u (p y)) (parent x))
      (sourceParentMark (fun y=>P.v (p y)) (parent x))
      (sourceParentMark (fun y=>P.s (p y)) (parent x))
      (sourceParentMark (fun y=>P.tau (p y)) (parent x)) := by
    apply sum_nonneg
    intro x hx
    apply mul_nonneg (h.probability x hx).1
    apply le_trans (hvalid _ _ _ _
      (h.probability_pos (fun y hy=>(hactivity y hy).1) hx)
      (h.probability_le_bound hactivity hx)
      (h.retention_bounds hactivity hx).1 (h.retention_bounds hactivity hx).2
      (h.parent_probability_bounds hactivity hx).1
      (h.parent_probability_bounds hactivity hx).2
      (h.response_at_probability_endpoint hactivity hx))
    exact h.message_scalar_le_marked (fun y hy=>(hactivity y hy).1)
      P hzero.1 hzero.2.1 lower b hx
  have hpos := h.exact_positive_capacity_budget_scaled hactivity
    (fun x=>P.u (p x)) (fun x hx=>(hweight x hx).1)
  have hneg := h.exact_negative_capacity_budget_scaled hactivity
    (fun x=>P.v (p x)) (fun x hx=>(hweight x hx).2.1)
  have hblock := h.weighted_blocking_capacity_budget hactivity
    (fun x=>P.s (p x)) (fun x hx=>(hweight x hx).2.2)
  have hflow := h.message_response_zero (fun x hx=>(hactivity x hx).1) P.tau
  have hcore := h.message_core_sum (fun x hx=>(hactivity x hx).1) P lower b
  have hphi : P.w*sourcePhiBudget G S activity p lower b≤0 := by
    rcases hlo with he|he
    · rw [he,zero_mul]
    · exact mul_nonpos_of_nonneg_of_nonpos hP.1
        (h.phi_budget_scaled hlower (fun x hx=>⟨he x hx,(hactivity x hx).2⟩))
  rw [hmean,sub_self,mul_zero,add_zero] at hcore
  simp only [messageSourceMarkedRow,mul_add,sum_add_distrib] at hrow
  simp only [mul_add,sum_add_distrib] at hflow
  linarith

/-- A real forest with uniform positive activity supplies every message and
moment used by the scalar source. The log reference need not be an activity
lower bound when the phi multiplier is zero. -/
theorem forest_message_variance_of_scalar_certificate
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V)
    {lower b activity : ℝ} (hlower : 0<lower) (hactivity : 0<activity)
    (hhi : activity≤b) (P : MessageSourceParameters) (hP : P.Admissible b)
    (hlo : P.w=0 ∨ lower≤activity)
    (hvalid : MessageSourceRowValid P lower b) :
    hardCoreVariance G S activity ≤
      P.CJ*hardCoreMarginalSelectionScore G S activity b+
      P.Cmu*hardCoreMean G S activity+
      (P.Dn-P.ell*Real.log (activity/lower))*(S.card:ℝ) := by
  let act : V→ℝ := fun _=>activity
  obtain ⟨parent,p,d,hm,hmean,hvar⟩ := exists_forest_source_messages_moments G hG S act
    (fun _=>1) (fun _ _=>hactivity.le)
  have hresponse : (∑x∈S,p x*d x)=∑x∈S,heterogeneousMarginal G S act x := by
    rw [←hmean,heterogeneousMean_marked_eq_sum_marginals]
    simp
  have hbound := hm.message_variance_sum_bound hlower (fun _ _=>⟨hactivity,hhi⟩)
    P hP (hlo.imp_right (fun he _ _=>he)) hresponse hvalid
  have hcard : markedSum (fun _ : V=> (1:ℝ))=(fun J:Finset V=>(J.card:ℝ)) := by
    funext J; simp [markedSum]
  rw [←hvar,hcard] at hbound
  have hroot : (∑x∈sourceRoots S parent,Real.log (1-p x))≤0 := by
    apply sum_nonpos
    intro x hx
    have hb := hm.probability x (mem_filter.mp hx).1
    exact Real.log_nonpos (by linarith) (by linarith)
  have hlog : (S.card:ℝ)*Real.log (activity/lower)≤
      ∑x∈S,sourceLogReference lower (p x) := by
    unfold sourceLogReference
    rw [hm.log_mass_identity (fun _ _=>hactivity) lower]
    simp only [act,sum_const,nsmul_eq_mul,Real.log_div hactivity.ne' hlower.ne']
    nlinarith
  have hmu : (∑x∈S,heterogeneousMarginal G S act x)=hardCoreMean G S activity := by
    simp only [act,heterogeneousMarginal_common]
    exact (hardCoreMean_eq_sum_vertex_marginals G S activity).symm
  have hscore : (∑x∈S,heterogeneousMarginal G S act x*
      selectionFraction (b/(1+b)) (heterogeneousMarginal G S act x))=
      hardCoreMarginalSelectionScore G S activity b := by
    simp only [act,heterogeneousMarginal_common,hardCoreMarginalSelectionScore]
  rw [hmu,hscore] at hbound
  simp only [act,heterogeneousVariance_common_card] at hbound
  nlinarith [mul_le_mul_of_nonneg_left hlog hP.2.1]

theorem IsMaximumMarginalIndependentOn.variance_le_mass_of_message_source
    {G : SimpleGraph V} {S I : Finset V} {lower b activity : ℝ}
    (hI : IsMaximumMarginalIndependentOn G S I activity) (hG : G.IsAcyclic)
    (hlower : 0<lower) (hactivity : 0<activity) (hhi : activity≤b)
    (P : MessageSourceParameters) (hP : P.Admissible b)
    (hCJ : 0≤P.CJ) (hCmu : 0≤P.Cmu) (hlo : P.w=0 ∨ lower≤activity)
    (hvalid : MessageSourceRowValid P lower b) :
    hardCoreVariance G S activity ≤
      (P.CJ+2*P.Cmu)*hardCoreOccupiedMass G S I activity+
      (P.Dn-P.ell*Real.log (activity/lower))*(S.card:ℝ) := by
  have hh := forest_message_variance_of_scalar_certificate G hG S
    hlower hactivity hhi P hP hlo hvalid
  have hs := mul_le_mul_of_nonneg_left (hI.forest_selection_bound hG hactivity hhi) hCJ
  have hhalf := hI.half_mean hG.isBipartite
  have hmu : hardCoreMean G S activity≤2*hardCoreOccupiedMass G S I activity := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hmu hCmu]

#print axioms SourceMessages.message_scalar_le_marked
#print axioms SourceMessages.message_core_sum
#print axioms SourceMessages.message_variance_sum_bound
#print axioms forest_message_variance_of_scalar_certificate
#print axioms IsMaximumMarginalIndependentOn.variance_le_mass_of_message_source
end ForestUnimodality
