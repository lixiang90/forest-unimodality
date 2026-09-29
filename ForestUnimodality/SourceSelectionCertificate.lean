import ForestUnimodality.SourceMixtureCertificate
import ForestUnimodality.MarginalSelectionBound

/-! Actual forest soundness for the stage900 selection source row.  The
continuous scalar predicate is explicit; no numerical row is presumed valid. -/
namespace ForestUnimodality
open Finset MarginalSelectionBound
variable {V : Type*} [DecidableEq V]

structure SelectionSourceParameters where
  CJ : ℝ
  Cmu : ℝ
  u : ℝ
  v : ℝ
  w : ℝ
  t : ℝ
  s : ℝ

def SelectionSourceParameters.Admissible (P : SelectionSourceParameters) : Prop :=
  0≤P.u ∧ 0≤P.v ∧ 0≤P.w ∧ 0≤P.s

/-- The existing phi budget differs by the zero response budget.  Accordingly
its response multiplier is t+w, not t. -/
noncomputable def SelectionSourceParameters.base (P : SelectionSourceParameters) : SourceRowParameters :=
  ⟨P.Cmu,0,0,P.w,P.t+P.w,P.s,(fun _=>P.u),(fun _=>P.v)⟩

noncomputable def sourceSelectionScalarRow (P : SelectionSourceParameters)
    (lower b p r z : ℝ) : ℝ :=
  P.CJ*r*selectionFraction (b/(1+b)) (p*r)+P.Cmu*r-r*(1-p)*z^2+
  P.u*((1/(p*sourceLogCapacity b p))*(max 0 (1-z))^2-(1-p/2)*(max 0 z)^2)+
  P.v*((1/(p*sourceLogCapacity b p))*(max 0 (z-1))^2-(1-p/2)*(max 0 (-z))^2)+
  P.w*(z-1+r*sourcePhi lower b p)+P.t*(z-r)+
  P.s*(r*((1-z)^2/sourceOddsCapacity b (sourceLogCapacity b p))-(1-r)*(1-p)*z^2)

def SelectionSourceRowValid (P : SelectionSourceParameters) (lower b : ℝ) : Prop :=
  ∀ p r z : ℝ, 0 < p → p ≤ b/(1+b) → 1/(1+b*(1-p)) ≤ r → r ≤ 1 →
    (p=b/(1+b) → z=1) → 0 ≤ sourceSelectionScalarRow P lower b p r z

theorem sourceSelectionScalarRow_eq_base (P : SelectionSourceParameters)
    (lower b p r z parentA : ℝ) :
    sourceSelectionScalarRow P lower b p r z =
      sourceScalarRow P.base lower b 1 parentA p r z+
        P.CJ*r*selectionFraction (b/(1+b)) (p*r) := by
  unfold sourceSelectionScalarRow sourceScalarRow SelectionSourceParameters.base
  ring

theorem sourceSelectionScalarRow_mul (P : SelectionSourceParameters)
    (lower b p pi z parentA : ℝ) (hp:p≠0) :
    p*sourceSelectionScalarRow P lower b p (pi/p) z =
      p*sourceScalarRow P.base lower b 1 parentA p (pi/p) z+
        P.CJ*(pi*selectionFraction (b/(1+b)) pi) := by
  rw [sourceSelectionScalarRow_eq_base P lower b p (pi/p) z parentA]
  have he : p*(pi/p)=pi := by field_simp
  rw [he]
  field_simp

theorem heterogeneousMarginal_common (G : SimpleGraph V) (S : Finset V) (z : ℝ) (x : V) :
    heterogeneousMarginal G S (fun _=>z) x=hardCoreVertexMarginal G S z x := by
  classical
  simp only [heterogeneousMarginal,heterogeneousMean,FiniteTilt.mean,FiniteTilt.numerator,
    FiniteTilt.total,heterogeneousWeight,prod_const,hardCoreVertexMarginal,partitionFunction,
    mul_ite,mul_one,mul_zero,sum_filter]

theorem heterogeneousVariance_common_card (G : SimpleGraph V) (S : Finset V) (z : ℝ) :
    heterogeneousVariance G S (fun _=>z) (fun J=>(J.card:ℝ))=hardCoreVariance G S z := by
  simp only [heterogeneousVariance,FiniteTilt.variance,FiniteTilt.covariance,FiniteTilt.mean,
    FiniteTilt.numerator,FiniteTilt.total,heterogeneousWeight,prod_const,
    hardCoreVariance,hardCoreSecondMoment,hardCoreMean,hardCoreMomentNumerator,
    pow_two,pow_one,partitionFunction,mul_comm]

/-- The scalar source predicate implies the actual total-occupancy variance
bound using the manuscript's already-defined marginal selection score. -/
theorem forest_selection_variance_of_scalar_certificate
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V)
    {lower b activity : ℝ} (hlower : 0<lower) (hlo : lower≤activity) (hhi : activity≤b)
    (P : SelectionSourceParameters) (hP : P.Admissible)
    (hvalid : SelectionSourceRowValid P lower b) :
    hardCoreVariance G S activity≤P.CJ*hardCoreMarginalSelectionScore G S activity b+
      P.Cmu*hardCoreMean G S activity := by
  let a : V→ℝ := fun _=>1
  let act : V→ℝ := fun _=>activity
  have hact : ∀x∈S, 0<act x ∧ act x≤b := fun _ _=>⟨hlower.trans_le hlo,hhi⟩
  obtain ⟨parent,p,d,hm,hmean,hvar⟩ := exists_forest_source_messages_moments G hG S act a
    (fun x hx=>(hact x hx).1.le)
  have hp : ∀x∈S,0<p x := fun x hx=>hm.probability_pos (fun y hy=>(hact y hy).1) hx
  have hrow : 0≤∑x∈S,p x*sourceSelectionScalarRow P lower b (p x)
      (heterogeneousMarginal G S act x/p x) (d x) := by
    apply sum_nonneg
    intro x hx
    apply mul_nonneg (hp x hx).le
    exact hvalid _ _ _ (hp x hx) (hm.probability_le_bound hact hx)
      (hm.retention_bounds hact hx).1 (hm.retention_bounds hact hx).2
      (hm.response_at_probability_endpoint hact hx)
  have hrows : (∑x∈S,p x*sourceSelectionScalarRow P lower b (p x)
      (heterogeneousMarginal G S act x/p x) (d x)) =
      (∑x∈S,p x*sourceScalarRow P.base lower b (a x) (sourceParentMark a (parent x))
        (p x) (heterogeneousMarginal G S act x/p x) (d x))+
      P.CJ*(∑x∈S,heterogeneousMarginal G S act x*
        selectionFraction (b/(1+b)) (heterogeneousMarginal G S act x)) := by
    rw [mul_sum,←sum_add_distrib]
    apply sum_congr rfl
    intro x hx
    exact sourceSelectionScalarRow_mul P lower b (p x) _ (d x) _ (hp x hx).ne'
  have hsum := source_scalar_row_sum G S act a parent p d P.base lower b
    (fun x hx=>(hp x hx).ne')
  have hpos := hm.positive_capacity_budget_scaled hact (fun _=>P.u) (fun _=>hP.1)
  have hneg := hm.negative_capacity_budget_scaled hact (fun _=>P.v) (fun _=>hP.2.1)
  have hphi := hm.phi_budget_scaled hlower (fun _ _=>⟨hlo,hhi⟩)
  have hblock := hm.blocking_capacity_budget_scaled hact
  have hresponse : (∑x∈S,p x*d x)-(∑x∈S,heterogeneousMarginal G S act x*a x)=0 := by
    rw [←hmean,heterogeneousMean_marked_eq_sum_marginals]
    exact sub_self _
  rw [hresponse,mul_zero,←hvar] at hsum
  have hphiPrice := mul_nonpos_of_nonneg_of_nonpos hP.2.2.1 hphi
  have hblockPrice := mul_nonpos_of_nonneg_of_nonpos hP.2.2.2 hblock
  have hcard : markedSum a=(fun J:Finset V=>(J.card:ℝ)) := by
    funext J
    simp [markedSum,a]
  have hmu : (∑x∈S,heterogeneousMarginal G S act x)=hardCoreMean G S activity := by
    simp only [act,heterogeneousMarginal_common]
    exact (hardCoreMean_eq_sum_vertex_marginals G S activity).symm
  have hscore : (∑x∈S,heterogeneousMarginal G S act x*
      selectionFraction (b/(1+b)) (heterogeneousMarginal G S act x))=
      hardCoreMarginalSelectionScore G S activity b := by
    simp only [act,heterogeneousMarginal_common,hardCoreMarginalSelectionScore]
  rw [hrows,hscore] at hrow
  simp only [SelectionSourceParameters.base,zero_mul,sub_zero,add_zero] at hsum
  rw [hcard] at hsum
  simp only [act,heterogeneousVariance_common_card] at hsum
  rw [hmu] at hsum
  change _ ≤ _ at hrow
  simp only [SelectionSourceParameters.base, act] at hrow hphiPrice hblockPrice
  linarith

theorem IsMaximumMarginalIndependentOn.variance_le_mass_of_selection_certificate
    {G : SimpleGraph V} {S I : Finset V} {activity lower b : ℝ}
    (hI : IsMaximumMarginalIndependentOn G S I activity) (hG : G.IsAcyclic)
    (hlower : 0<lower) (hlo : lower≤activity) (hhi : activity≤b)
    (P : SelectionSourceParameters) (hP : P.Admissible) (hCJ : 0≤P.CJ) (hCmu : 0≤P.Cmu)
    (hvalid : SelectionSourceRowValid P lower b) :
    hardCoreVariance G S activity≤(P.CJ+2*P.Cmu)*hardCoreOccupiedMass G S I activity :=
  hI.variance_le_mass_of_joint_bound hG.isBipartite (hlower.trans_le hlo) hhi hCJ hCmu
    (forest_selection_variance_of_scalar_certificate G hG S hlower hlo hhi P hP hvalid)

#print axioms sourceSelectionScalarRow_eq_base
#print axioms heterogeneousVariance_common_card
#print axioms forest_selection_variance_of_scalar_certificate
#print axioms IsMaximumMarginalIndependentOn.variance_le_mass_of_selection_certificate
end ForestUnimodality
