import ForestUnimodality.NonnegativeSourceCertificate
import ForestUnimodality.LaplaceRateInterval
import ForestUnimodality.SourceMixtureCertificate

/-! The old support-size affine source, valid for all positive heterogeneous
activities below one upper cap. There is no positive lower-activity cutoff. -/
namespace ForestUnimodality
open Finset Filter Set
open scoped Topology

structure AffineSourceParameters where
  A : ℝ
  C : ℝ
  u : ℝ
  v : ℝ
  s : ℝ

def AffineSourceParameters.Admissible (P : AffineSourceParameters) : Prop :=
  0 ≤ P.u ∧ 0 ≤ P.v ∧ 0 ≤ P.s

noncomputable def affineSourceRow (P : AffineSourceParameters)
    (b p r a d : ℝ) : ℝ :=
  P.A*a^2/p + P.C*r*a^2 - r*(1-p)*d^2 +
  P.u*((1/(p*sourceLogCapacity b p))*(max 0 (a-d))^2-(1-p/2)*(max 0 d)^2) +
  P.v*((1/(p*sourceLogCapacity b p))*(max 0 (d-a))^2-(1-p/2)*(max 0 (-d))^2) +
  P.s*(r*((a-d)^2/sourceOddsCapacity b (sourceLogCapacity b p))-(1-r)*(1-p)*d^2)

def AffineSourceRowValid (P : AffineSourceParameters) (b : ℝ) : Prop :=
  ∀ p r d : ℝ, 0 < p → p ≤ b/(1+b) →
    1/(1+b*(1-p)) ≤ r → r ≤ 1 →
    (p=b/(1+b) → d=1) → 0 ≤ affineSourceRow P b p r 1 d

theorem affineSourceRow_scale (P : AffineSourceParameters) {b p r a d : ℝ}
    (ha : 0<a) :
    affineSourceRow P b p r a d = a^2*affineSourceRow P b p r 1 (d/a) := by
  have hmax (x : ℝ) : max 0 (x/a)=max 0 x/a := by
    simpa only [zero_div] using max_div_div_right ha.le 0 x
  have h₁ : 1-d/a=(a-d)/a := by field_simp
  have h₂ : d/a-1=(d-a)/a := by field_simp
  have h₃ : -(d/a)=(-d)/a := by ring
  simp only [affineSourceRow, h₁, h₂, h₃, hmax]
  field_simp [ha.ne']

theorem AffineSourceRowValid.homogeneous {P : AffineSourceParameters} {b p r a d : ℝ}
    (h : AffineSourceRowValid P b) (hp : 0<p) (hpq : p≤b/(1+b))
    (hrlo : 1/(1+b*(1-p))≤r) (hrhi : r≤1) (ha : 0≤a)
    (hend : p=b/(1+b) → d=a) : 0≤affineSourceRow P b p r a d := by
  have hpos (a : ℝ) (ha : 0<a) (he : p=b/(1+b) → d=a) :
      0≤affineSourceRow P b p r a d := by
    rw [affineSourceRow_scale P ha]
    exact mul_nonneg (sq_nonneg a)
      (h p r (d/a) hp hpq hrlo hrhi (fun hq=>by rw [he hq]; exact div_self ha.ne'))
  by_cases ha0 : a=0
  · subst a
    by_cases he : p=b/(1+b)
    · have hd := hend he
      simp [hd, affineSourceRow]
    · have hf : ContinuousAt (fun t : ℝ=>affineSourceRow P b p r t d) 0 := by
        unfold affineSourceRow
        fun_prop
      apply ge_of_tendsto (hf.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0))
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact hpos t ht (fun hq=>False.elim (he hq))
  · exact hpos a (lt_of_le_of_ne ha (Ne.symm ha0)) hend

variable {V : Type*} [DecidableEq V]

/-- The source is true for any nonnegative marks and any strictly positive
heterogeneous activities up to b. All response and retention budgets are
derived from the actual forest distribution. -/
theorem forest_affine_source_variance_pos
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) (activity a : V→ℝ)
    {b : ℝ} (hactivity : ∀x∈S, 0<activity x ∧ activity x≤b)
    (ha : ∀x∈S, 0≤a x) (P : AffineSourceParameters) (hP : P.Admissible)
    (hvalid : AffineSourceRowValid P b) :
    heterogeneousVariance G S activity (markedSum a) ≤
      P.A*(∑x∈S, a x^2)+P.C*(∑x∈S, heterogeneousMarginal G S activity x*a x^2) := by
  obtain ⟨parent,p,d,hm,hmean,hvar⟩ := exists_forest_source_messages_moments G hG S activity a
    (fun x hx=>(hactivity x hx).1.le)
  have hp : ∀x∈S,0<p x := fun x hx=>hm.probability_pos (fun y hy=>(hactivity y hy).1) hx
  have hrows : 0≤∑x∈S,p x*affineSourceRow P b (p x)
      (heterogeneousMarginal G S activity x/p x) (a x) (d x) := by
    apply sum_nonneg
    intro x hx
    exact mul_nonneg (hp x hx).le (hvalid.homogeneous (hp x hx)
      (hm.probability_le_bound hactivity hx) (hm.retention_bounds hactivity hx).1
      (hm.retention_bounds hactivity hx).2 (ha x hx)
      (hm.response_at_probability_endpoint hactivity hx))
  have hpos := hm.positive_capacity_budget_scaled hactivity (fun _=>P.u) (fun _=>hP.1)
  have hneg := hm.negative_capacity_budget_scaled hactivity (fun _=>P.v) (fun _=>hP.2.1)
  have hblock : P.s*sourceBlockingBudget G S activity a p d b ≤ 0 := by
    have hb := mul_nonpos_of_nonneg_of_nonpos hP.2.2 (hm.blocking_capacity_budget hactivity)
    convert hb using 1
    congr 1
    unfold sourceBlockingBudget
    congr 1
    apply sum_congr rfl
    intro x hx
    field_simp [(hp x hx).ne']
  have he : (∑x∈S,p x*affineSourceRow P b (p x)
      (heterogeneousMarginal G S activity x/p x) (a x) (d x)) =
      P.A*(∑x∈S,a x^2)+P.C*(∑x∈S,heterogeneousMarginal G S activity x*a x^2)-
      (∑x∈S,heterogeneousMarginal G S activity x*(1-p x)*d x^2)+
      sourcePositiveCapacityBudget S a parent p d b (fun _=>P.u)+
      sourceNegativeCapacityBudget S a parent p d b (fun _=>P.v)+
      P.s*sourceBlockingBudget G S activity a p d b := by
    simp only [sourcePositiveCapacityBudget,sourceNegativeCapacityBudget,sourceBlockingBudget,
      ←sum_add_distrib,←sum_sub_distrib,mul_sum]
    apply sum_congr rfl
    intro x hx
    unfold affineSourceRow
    field_simp [(hp x hx).ne']
  rw [he,←hvar] at hrows
  linarith

/-- Indicator specialization. No independence of B is required for the
source itself; independence is used later by the available-count mixture. -/
theorem forest_marked_affine_source_variance
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S B : Finset V) (hBS : B⊆S)
    (activity : V→ℝ) {b : ℝ} (hactivity : ∀x∈S,0<activity x ∧ activity x≤b)
    (P : AffineSourceParameters) (hP : P.Admissible) (hvalid : AffineSourceRowValid P b) :
    heterogeneousVariance G S activity (fun J=>((J∩B).card:ℝ)) ≤
      P.A*(B.card:ℝ)+P.C*heterogeneousMean G S activity (fun J=>((J∩B).card:ℝ)) := by
  classical
  have h := forest_affine_source_variance_pos G hG S activity (sourceIndicator B) hactivity
    (fun x _=>by unfold sourceIndicator; split <;> norm_num) P hP hvalid
  have hf : S.filter (fun x=>x∈B)=B := by
    ext x
    simp only [mem_filter]
    exact ⟨And.right,fun hx=>⟨hBS hx,hx⟩⟩
  have he : markedSum (sourceIndicator B)=(fun J=>((J∩B).card:ℝ)) :=
    funext (markedSum_sourceIndicator B)
  have hsq (x : V) : (sourceIndicator B x)^2=sourceIndicator B x := by
    unfold sourceIndicator
    split <;> norm_num
  have hsum : (∑x∈S,(sourceIndicator B x)^2)=(B.card:ℝ) := by
    simp only [sourceIndicator,ite_pow,one_pow,zero_pow (by decide : 2≠0),←sum_filter,hf]
    simp
  have hmean := heterogeneousMean_marked_eq_sum_marginals G S activity (sourceIndicator B)
  rw [hsum] at h
  simpa only [hsq,←hmean,he] using h

/-- The same fixed B works along the entire downward exponential tilt.
In particular no source lower endpoint is asserted for tilted activities. -/
theorem forest_marked_affine_source_tilt
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S B : Finset V) (hBS : B⊆S)
    {z b : ℝ} (hz : 0<z) (hzb : z≤b)
    (P : AffineSourceParameters) (hP : P.Admissible) (hvalid : AffineSourceRowValid P b) :
    ∀t≥0, heterogeneousVariance G S (independentTiltActivities B z (Real.exp (-t)))
      (fun J=>((J∩B).card:ℝ)) ≤ P.A*(B.card:ℝ)+
      P.C*heterogeneousMean G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J=>((J∩B).card:ℝ)) := by
  intro t ht
  apply forest_marked_affine_source_variance G hG S B hBS _ ?_ P hP hvalid
  intro x _
  have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
  unfold independentTiltActivities
  split_ifs
  · exact ⟨mul_pos (Real.exp_pos _) hz,(by nlinarith : Real.exp (-t)*z≤z).trans hzb⟩
  · exact ⟨hz,hzb⟩

theorem hardCoreMarkedVariance_le_affine_source_certificate
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S B : Finset V) (hBS : B⊆S)
    {z b : ℝ} (hz : 0<z) (hzb : z≤b)
    (P : AffineSourceParameters) (hP : P.Admissible) (hvalid : AffineSourceRowValid P b) :
    hardCoreMarkedVariance G S B z ≤ P.A*(B.card:ℝ)+P.C*hardCoreOccupiedMass G S B z := by
  have h := forest_marked_affine_source_variance G hG S B hBS (fun _=>z)
    (fun _ _=>⟨hz,hzb⟩) P hP hvalid
  simpa only [hardCoreMarkedVariance,heterogeneousMean_common_intersection] using h

/-- A single certified affine source and endpoint rates imply the actual
available-count lower tail throughout an activity interval. -/
theorem IsMaximumMarginalIndependentOn.lowerTail_le_affine_source_certificate
    {G : SimpleGraph V} {S B : Finset V} {z b ρ α u rate lo hi : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hzb : z≤b) (hρ : 0<ρ) (hρq : ρ≤z/(1+z))
    (P : AffineSourceParameters) (hP : P.Admissible) (hvalid : AffineSourceRowValid P b)
    (hA : 0≤P.A) (hC : 0<P.C) (hu : 0≤u) (hα : 0≤α)
    (hdensity : ρ*(S.card:ℝ)≤hardCoreMean G S z)
    (hlo : 0≤lo) (hhi : hi≤1) (hq : z/(1+z)∈Icc lo hi)
    (hrlo : rate≤AffineLaplace.tailRate P.A P.C ρ α u lo)
    (hrhi : rate≤AffineLaplace.tailRate P.A P.C ρ α u hi) :
    hardCoreAvailableLowerTail G S B z (α*hardCoreAvailableMean G S B z) ≤
      Real.exp (-rate*hardCoreAvailableMean G S B z) := by
  apply hB.lowerTail_le_rate hG hz hρ hρq hA hC hu hdensity
  · intro t ht
    exact forest_marked_affine_source_tilt G hG S B hB.subset hz hzb P hP hvalid t ht.1
  · exact AffineLaplace.tailRate_lower_of_endpoints P.A P.C ρ hα hu hlo hhi
      (hq.1.trans hq.2) hrlo hrhi hq

#print axioms AffineSourceRowValid.homogeneous
#print axioms forest_affine_source_variance_pos
#print axioms forest_marked_affine_source_tilt
#print axioms IsMaximumMarginalIndependentOn.lowerTail_le_affine_source_certificate
end ForestUnimodality
