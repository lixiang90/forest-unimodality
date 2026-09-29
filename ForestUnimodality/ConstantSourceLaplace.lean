import ForestUnimodality.NonnegativeSourceCertificate
import ForestUnimodality.GaussianFiniteStep
import ForestUnimodality.LaplaceRateInterval

/-! Constant variance sources integrated along the actual fixed-mark tilt.
This is the C=0 case, including the genuine available-count Chernoff bound. -/
namespace ForestUnimodality.FiniteTilt
open Set

theorem log_laplace_le_of_constant_variance {α : Type*} (s : Finset α) (w X : α→ℝ)
    (hw : ∀x∈s, 0≤w x) (hZ : 0<total s w) {D u : ℝ} (hu : 0≤u)
    (hv : ∀t∈Icc 0 u, variance s (tilt w (fun x=>-X x) t) X≤D) :
    Real.log (total s (tilt w (fun x=>-X x) u)/total s w)≤-mean s w X*u+D*u^2/2 := by
  have hz (t : ℝ) := total_tilt_pos s w (fun x=>-X x) hw hZ t
  have hd (t : ℝ) : HasDerivAt (fun t=>mean s (tilt w (fun x=>-X x) t) X)
      (-variance s (tilt w (fun x=>-X x) t) X) t := by
    simpa only [covariance_neg_right, variance] using
      hasDerivAt_mean s w (fun x=>-X x) X t (hz t).ne'
  have hlog (t : ℝ) : HasDerivAt (fun t=>Real.log (total s (tilt w (fun x=>-X x) t)))
      (-mean s (tilt w (fun x=>-X x) t) X) t := by
    have h := (hasDerivAt_total s w (fun x=>-X x) t).log (hz t).ne'
    change HasDerivAt _ (mean s (tilt w (fun x=>-X x) t) (fun x=>-X x)) t at h
    simpa only [mean_neg] using h
  have hdneg (t : ℝ) : HasDerivAt (fun t=>-mean s (tilt w (fun x=>-X x) t) X)
      (variance s (tilt w (fun x=>-X x) t) X) t := by
    convert (hd t).neg using 1
    all_goals first | rfl | simp
  have h := GaussianFiniteStep.finite_step_lower (G := -D) (c:=0) hu
    (fun t _=>hlog t) (fun t _=>hdneg t)
    (fun t ht=>by simpa using neg_le_neg (hv t ht))
  have ht : tilt w (fun x=>-X x) 0=w := by funext x; simp [tilt]
  rw [ht] at h
  rw [Real.log_div (hz u).ne' hZ.ne']
  nlinarith

#print axioms log_laplace_le_of_constant_variance
end ForestUnimodality.FiniteTilt

namespace ForestUnimodality
open Finset Set
variable {V : Type*} [DecidableEq V]

theorem forest_independent_constant_source_variance
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S B : Finset V) (hBS : B⊆S) (activity : V→ℝ)
    {b A u v : ℝ} (hb : 0<b) (hactivity : ∀x∈S, 0≤activity x ∧ activity x≤b)
    (hu : 0≤u) (hv : 0≤v) (hvalid : NonnegativeSourceRowValid b A u v) :
    heterogeneousVariance G S activity (fun J=>((J∩B).card:ℝ))≤A*(B.card:ℝ) := by
  classical
  have h := forest_nonnegative_source_variance G hG S activity (sourceIndicator B) hb hactivity
    (fun x _=>by unfold sourceIndicator; split <;> norm_num) hu hv hvalid
  have hf : S.filter (fun x=>x∈B)=B := by
    ext x
    simp only [mem_filter]
    exact ⟨And.right,fun hx=>⟨hBS hx,hx⟩⟩
  have hsum : (∑x∈S, (sourceIndicator B x)^2)=(B.card:ℝ) := by
    simp only [sourceIndicator, ite_pow, one_pow, zero_pow (by decide : 2≠0), ← sum_filter, hf]
    simp
  have he : markedSum (sourceIndicator B)=(fun J=>((J∩B).card:ℝ)) := funext (markedSum_sourceIndicator B)
  simpa only [hsum, he] using h

theorem log_hardCoreLayerLaplace_le_constant (G : SimpleGraph V) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V)) {z u D : ℝ} (hz : 0<z) (hu : 0≤u)
    (hsource : ∀t∈Icc 0 u,
      heterogeneousVariance G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J=>((J∩B).card:ℝ))≤D) :
    Real.log (hardCoreLayerLaplace G S B z (Real.exp (-u)))≤-hardCoreOccupiedMass G S B z*u+D*u^2/2 := by
  let w : Finset V→ℝ := heterogeneousWeight (fun _=>z)
  let X : Finset V→ℝ := fun J=>((J∩B).card:ℝ)
  have hweight (t : ℝ) : heterogeneousWeight (independentTiltActivities B z (Real.exp (-t))) =
      FiniteTilt.tilt w (fun J=>-X J) t := by funext J; exact independent_tilt_weight_eq B J z t
  have hw : ∀J∈independentSubsets G S, 0≤w J := by
    intro J _
    exact heterogeneousWeight_nonneg (fun _ _=>hz.le)
  have hZ : FiniteTilt.total (independentSubsets G S) w=partitionFunction G S z := by
    simp only [FiniteTilt.total,w,heterogeneousWeight,prod_const,partitionFunction]
  have hm : FiniteTilt.mean (independentSubsets G S) w X=hardCoreOccupiedMass G S B z := by
    rw [hardCoreOccupiedMass_eq_intersection_expectation]
    simp only [FiniteTilt.mean,FiniteTilt.numerator,hZ,w,X,heterogeneousWeight,prod_const]
    congr 1
    apply sum_congr rfl
    intro J _
    ring
  have hs : ∀t∈Icc 0 u, FiniteTilt.variance (independentSubsets G S)
      (FiniteTilt.tilt w (fun J=>-X J) t) X≤D := by
    intro t ht
    simpa only [heterogeneousVariance,hweight t] using hsource t ht
  have h := FiniteTilt.log_laplace_le_of_constant_variance (independentSubsets G S) w X hw
    (hZ ▸ partitionFunction_pos G S hz.le) hu hs
  rw [hm,hZ,←hweight u] at h
  rw [hardCoreLayerLaplace_eq_heterogeneous_ratio G S B hBS hB hz]
  exact h

theorem hardCoreLayerLaplace_le_exp_constant (G : SimpleGraph V) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V)) {z u D : ℝ} (hz : 0<z) (hu : 0≤u)
    (hsource : ∀t∈Icc 0 u,
      heterogeneousVariance G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J=>((J∩B).card:ℝ))≤D) :
    hardCoreLayerLaplace G S B z (Real.exp (-u))≤Real.exp (-hardCoreOccupiedMass G S B z*u+D*u^2/2) := by
  have hp : 0<hardCoreLayerLaplace G S B z (Real.exp (-u)) := by
    rw [hardCoreLayerLaplace_eq_heterogeneous_ratio G S B hBS hB hz]
    apply div_pos _ (partitionFunction_pos G S hz.le)
    apply heterogeneousPartition_pos
    intro x _
    unfold independentTiltActivities
    split <;> positivity
  exact (Real.log_le_iff_le_exp hp).mp (log_hardCoreLayerLaplace_le_constant G S B hBS hB hz hu hsource)

omit [DecidableEq V] in
theorem log_bernoulli_laplace_lower {q : ℝ} (hq0 : 0≤q) (hq1 : q≤1) (u : ℝ) :
    -q*u≤Real.log (1-q+q*Real.exp (-u)) := by
  have h := (StrictConcaveOn.concaveOn strictConcaveOn_log_Ioi).2
    (by norm_num : (1:ℝ)∈Set.Ioi 0) (Real.exp_pos (-u))
    (by linarith : 0≤1-q) hq0 (by ring : 1-q+q=1)
  simpa only [smul_eq_mul, mul_one, Real.log_one, Real.log_exp, mul_zero, zero_add,
    mul_neg, neg_mul] using h

theorem hardCoreAvailableLowerTail_le_exp_constant (G : SimpleGraph V) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V)) {z u D threshold : ℝ}
    (hz : 0<z) (hu : 0≤u) (ht : 0≤threshold)
    (hsource : ∀t∈Icc 0 u,
      heterogeneousVariance G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J=>((J∩B).card:ℝ))≤D) :
    hardCoreAvailableLowerTail G S B z threshold≤
      Real.exp (threshold*(z/(1+z))*u-hardCoreOccupiedMass G S B z*u+D*u^2/2) := by
  have hq0 : 0<z/(1+z) := by positivity
  have hq1 : z/(1+z)<1 := (div_lt_one (by positivity)).mpr (by linarith)
  have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu)
  have hr0 : 0<1-z/(1+z)+z/(1+z)*Real.exp (-u) := by positivity
  have hr1 : 1-z/(1+z)+z/(1+z)*Real.exp (-u)≤1 := by nlinarith
  have h := hardCoreAvailableLowerTail_le_laplace G S B hz.le hr0 hr1 threshold
  have hL := hardCoreLayerLaplace_le_exp_constant G S B hBS hB hz hu hsource
  have hh := h.trans (mul_le_mul_of_nonneg_left hL (Real.exp_pos _).le)
  rw [←Real.exp_add] at hh
  apply hh.trans
  apply Real.exp_le_exp.mpr
  have hl := mul_le_mul_of_nonneg_left (log_bernoulli_laplace_lower hq0.le hq1.le u) ht
  nlinarith

/-- The optimized quadratic bound retains the same original m in the
variance source, real cutoff and exponential rate. -/
theorem hardCoreAvailableLowerTail_le_gaussian_rate (G : SimpleGraph V) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V)) {z C α : ℝ}
    (hz : 0<z) (hC : 0<C) (hα0 : 0≤α) (hα1 : α≤1)
    (hsource : ∀t≥0,
      heterogeneousVariance G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J=>((J∩B).card:ℝ))≤C*hardCoreAvailableMean G S B z) :
    hardCoreAvailableLowerTail G S B z (α*hardCoreAvailableMean G S B z)≤
      Real.exp (-((z/(1+z))^2*(1-α)^2/(2*C))*hardCoreAvailableMean G S B z) := by
  let q := z/(1+z)
  let t := q*(1-α)/C
  have hq : 0<q := by dsimp [q]; positivity
  have ht : 0≤t := div_nonneg (mul_nonneg hq.le (sub_nonneg.mpr hα1)) hC.le
  have hm := hardCoreAvailableMean_nonneg G S B hz.le
  have h := hardCoreAvailableLowerTail_le_exp_constant G S B hBS hB hz ht (mul_nonneg hα0 hm)
    (fun s hs=>hsource s hs.1)
  rw [hardCoreOccupiedMass_eq_activity_available_mean G S B hBS hB hz] at h
  convert h using 1
  congr 1
  dsimp [t,q]
  field_simp
  ring

/-- A certified nonnegative source supplies the whole heterogeneous tilt
path. The independent set is selected once at the original activity. -/
theorem IsMaximumMarginalIndependentOn.lowerTail_of_nonnegative_source
    {G : SimpleGraph V} {S B : Finset V} {z b A u v C ρ α : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hzb : z≤b) (hA : 0≤A) (hu : 0≤u) (hv : 0≤v)
    (hvalid : NonnegativeSourceRowValid b A u v)
    (hρ : 0<ρ) (hρq : ρ≤z/(1+z)) (hdensity : ρ*(S.card:ℝ)≤hardCoreMean G S z)
    (hC : 0<C) (hCbound : A*(2*(z/(1+z))/ρ-1)≤C) (hα0 : 0≤α) (hα1 : α≤1) :
    hardCoreAvailableLowerTail G S B z (α*hardCoreAvailableMean G S B z)≤
      Real.exp (-((z/(1+z))^2*(1-α)^2/(2*C))*hardCoreAvailableMean G S B z) := by
  apply hardCoreAvailableLowerTail_le_gaussian_rate G S B hB.subset hB.independent hz hC hα0 hα1
  intro t ht
  have hact : ∀x∈S, 0 ≤ independentTiltActivities B z (Real.exp (-t)) x ∧
      independentTiltActivities B z (Real.exp (-t)) x≤b := by
    intro x _
    have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
    unfold independentTiltActivities
    split_ifs
    · exact ⟨mul_nonneg (Real.exp_pos _).le hz.le,
        (by nlinarith : Real.exp (-t)*z≤z).trans hzb⟩
    · exact ⟨hz.le,hzb⟩
  have hs := forest_independent_constant_source_variance G hG S B hB.subset
    (independentTiltActivities B z (Real.exp (-t))) (hz.trans_le hzb) hact hu hv hvalid
  have hcard := hB.card_le_available_of_density hG hz hρ hρq hdensity
  have hm := hardCoreAvailableMean_nonneg G S B hz.le
  apply hs.trans
  calc
    A*(B.card:ℝ)≤A*((2*(z/(1+z))/ρ-1)*hardCoreAvailableMean G S B z) :=
      mul_le_mul_of_nonneg_left hcard hA
    _ = (A*(2*(z/(1+z))/ρ-1))*hardCoreAvailableMean G S B z := by ring
    _ ≤ C*hardCoreAvailableMean G S B z := mul_le_mul_of_nonneg_right hCbound hm

#print axioms forest_independent_constant_source_variance
#print axioms log_hardCoreLayerLaplace_le_constant
#print axioms hardCoreAvailableLowerTail_le_gaussian_rate
#print axioms IsMaximumMarginalIndependentOn.lowerTail_of_nonnegative_source
end ForestUnimodality
