import ForestUnimodality.IndependentCountLaplace
import ForestUnimodality.AffineSourceLaplaceRate

/-! Closed-step flow comparison on one fixed tilt.  A negative derivative
improves the end of a step, but never replaces the whole-step bound.  Endpoint
and log-Laplace charges can use different valid affine variance sources. -/
namespace ForestUnimodality.PiecewiseFlowLaplace
open Set Finset

/-- Signed derivative bound, with no assumption that the derivative is positive. -/
theorem endpoint_upper {f df : ℝ → ℝ} {a b U d : ℝ} (hab : a ≤ b)
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (df t) t)
    (hdf : ∀ t ∈ Icc a b, df t ≤ d) (ha : f a ≤ U) :
    f b ≤ U+d*(b-a) := by
  let g := fun t => f t-d*t
  have hg (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt g (df t-d) t :=
    by
    convert (hd t ht).sub ((hasDerivAt_id t).const_mul d) using 1 <;> first | rfl | ring
  have hm : AntitoneOn g (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · intro t ht; exact (hg t ht).continuousAt.continuousWithinAt
    · intro t ht; exact (hg t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hg t (interior_subset ht)).deriv]
      exact sub_nonpos.mpr (hdf t (interior_subset ht))
  have hh := hm ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab
  dsimp [g] at hh
  nlinarith

/-- The whole-step price uses max(0,d), including when the endpoint falls. -/
theorem whole_step_upper {f df : ℝ → ℝ} {a b U d : ℝ} (_hab : a ≤ b)
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (df t) t)
    (hdf : ∀ t ∈ Icc a b, df t ≤ d) (ha : f a ≤ U) :
    ∀ t ∈ Icc a b, f t ≤ U+max 0 d*(b-a) := by
  intro t ht
  have hh := endpoint_upper ht.1 (fun s hs => hd s ⟨hs.1,hs.2.trans ht.2⟩)
    (fun s hs => hdf s ⟨hs.1,hs.2.trans ht.2⟩) ha
  have h₁ := mul_le_mul_of_nonneg_right (le_max_right 0 d) (sub_nonneg.mpr ht.1)
  have h₂ := mul_le_mul_of_nonneg_left (show t-a ≤ b-a by linarith [ht.2]) (le_max_left 0 d)
  linarith

theorem decayIntegral_nonneg {C u : ℝ} (hC : 0<C) (hu : 0≤u) :
    0≤AffineLaplace.decayIntegral C u := by
  unfold AffineLaplace.decayIntegral
  apply div_nonneg _ hC.le
  exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith))

/-- The two exact scalar formulas evaluated by each rational flow cell. -/
noncomputable def endLower (L D C duration : ℝ) : ℝ :=
  (L+D/C)*Real.exp (-C*duration)-D/C
noncomputable def integralLower (L D C duration : ℝ) : ℝ :=
  L*AffineLaplace.decayIntegral C duration-D/C*(duration-AffineLaplace.decayIntegral C duration)

theorem affine_endpoint {w v : ℝ → ℝ} {a b L D C : ℝ} (hab : a≤b)
    (hC : 0<C) (hd : ∀t∈Icc a b, HasDerivAt w (-v t) t)
    (hv : ∀t∈Icc a b, v t≤D+C*w t) (hL : L≤w a) :
    endLower L D C (b-a)≤w b := by
  have hh := AffineLaplace.mean_lower hC (sub_nonneg.mpr hab)
    (w:=fun t=>w (a+t)) (v:=fun t=>v (a+t))
    (fun t ht=>by
      simpa only [Function.comp_def, mul_one] using (hd (a+t) ⟨by linarith [ht.1],by linarith [ht.2]⟩).comp t
        ((hasDerivAt_id t).const_add a))
    (fun t ht=>hv (a+t) ⟨by linarith [ht.1],by linarith [ht.2]⟩)
  simp only [add_zero,add_sub_cancel] at hh
  have hm := mul_le_mul_of_nonneg_right hL (Real.exp_pos (-C*(b-a))).le
  unfold endLower
  nlinarith

theorem affine_log_step {w v logZ : ℝ → ℝ} {a b L D C : ℝ} (hab : a≤b)
    (hC : 0<C) (hd : ∀t∈Icc a b, HasDerivAt w (-v t) t)
    (hlog : ∀t∈Icc a b, HasDerivAt logZ (-w t) t)
    (hv : ∀t∈Icc a b, v t≤D+C*w t) (hL : L≤w a) :
    logZ b-logZ a≤-integralLower L D C (b-a) := by
  have hh := AffineLaplace.log_lower_tilt_bound hC (sub_nonneg.mpr hab)
    (w:=fun t=>w (a+t)) (v:=fun t=>v (a+t)) (L:=fun t=>logZ (a+t))
    (fun t ht=>by
      simpa only [Function.comp_def, mul_one] using (hd (a+t) ⟨by linarith [ht.1],by linarith [ht.2]⟩).comp t
        ((hasDerivAt_id t).const_add a))
    (fun t ht=>by
      simpa only [Function.comp_def, mul_one] using (hlog (a+t) ⟨by linarith [ht.1],by linarith [ht.2]⟩).comp t
        ((hasDerivAt_id t).const_add a))
    (fun t ht=>hv (a+t) ⟨by linarith [ht.1],by linarith [ht.2]⟩)
  simp only [add_zero,add_sub_cancel] at hh
  have hm := mul_le_mul_of_nonneg_right hL (decayIntegral_nonneg hC (sub_nonneg.mpr hab))
  unfold integralLower
  nlinarith

/-- All values denote bounds on the same actual w and logZ. In particular the
endpoint and integral certificates may choose different affine sources. -/
theorem chain {w v logZ : ℝ → ℝ} (time lower charge DE CE DI CI : ℕ → ℝ)
    (n : ℕ) (hstart : lower 0≤w (time 0))
    (horder : ∀i<n, time i≤time (i+1))
    (hd : ∀i<n, ∀t∈Icc (time i) (time (i+1)), HasDerivAt w (-v t) t)
    (hlog : ∀i<n, ∀t∈Icc (time i) (time (i+1)), HasDerivAt logZ (-w t) t)
    (hCE : ∀i<n, 0<CE i) (hCI : ∀i<n, 0<CI i)
    (hVE : ∀i<n, ∀t∈Icc (time i) (time (i+1)), v t≤DE i+CE i*w t)
    (hVI : ∀i<n, ∀t∈Icc (time i) (time (i+1)), v t≤DI i+CI i*w t)
    (hend : ∀i<n, lower (i+1)≤endLower (lower i) (DE i) (CE i) (time (i+1)-time i))
    (hcharge : ∀i<n, charge i ≤ integralLower (lower i) (DI i) (CI i) (time (i+1)-time i)) :
    lower n≤w (time n) ∧ logZ (time n)-logZ (time 0)≤-∑i∈range n, charge i := by
  induction n with
  | zero => simpa using hstart
  | succ n ih =>
    have hh := ih (fun i hi=>horder i (by omega))
      (fun i hi=>hd i (by omega)) (fun i hi=>hlog i (by omega))
      (fun i hi=>hCE i (by omega)) (fun i hi=>hCI i (by omega))
      (fun i hi=>hVE i (by omega)) (fun i hi=>hVI i (by omega))
      (fun i hi=>hend i (by omega)) (fun i hi=>hcharge i (by omega))
    have he := affine_endpoint (horder n (by omega)) (hCE n (by omega))
      (hd n (by omega)) (hVE n (by omega)) hh.1
    have hl := affine_log_step (horder n (by omega)) (hCI n (by omega))
      (hd n (by omega)) (hlog n (by omega)) (hVI n (by omega)) hh.1
    constructor
    · exact (hend n (by omega)).trans he
    · rw [sum_range_succ]
      have hc := hcharge n (by omega)
      linarith [hh.2]

/-- Specialization to the actual finite exponential family. Only affine
variance sources remain premises; neither an ODE trajectory nor a Laplace
bound is assumed. The mark X is fixed for the entire chain. -/
theorem finite_log_laplace_chain {α : Type*} (s : Finset α) (weight X : α → ℝ)
    (hw : ∀x∈s, 0≤weight x) (hZ : 0<FiniteTilt.total s weight)
    (time lower charge DE CE DI CI : ℕ → ℝ) (n : ℕ)
    (hzero : time 0=0) (hstart : lower 0≤FiniteTilt.mean s weight X)
    (horder : ∀i<n, time i≤time (i+1))
    (hCE : ∀i<n, 0<CE i) (hCI : ∀i<n, 0<CI i)
    (hVE : ∀i<n, ∀t∈Icc (time i) (time (i+1)),
      FiniteTilt.variance s (FiniteTilt.tilt weight (fun x=>-X x) t) X ≤
        DE i+CE i*FiniteTilt.mean s (FiniteTilt.tilt weight (fun x=>-X x) t) X)
    (hVI : ∀i<n, ∀t∈Icc (time i) (time (i+1)),
      FiniteTilt.variance s (FiniteTilt.tilt weight (fun x=>-X x) t) X ≤
        DI i+CI i*FiniteTilt.mean s (FiniteTilt.tilt weight (fun x=>-X x) t) X)
    (hend : ∀i<n, lower (i+1)≤endLower (lower i) (DE i) (CE i) (time (i+1)-time i))
    (hcharge : ∀i<n, charge i ≤ integralLower (lower i) (DI i) (CI i) (time (i+1)-time i)) :
    Real.log (FiniteTilt.total s (FiniteTilt.tilt weight (fun x=>-X x) (time n)) /
      FiniteTilt.total s weight) ≤ -∑i∈range n, charge i := by
  let w := fun t=>FiniteTilt.mean s (FiniteTilt.tilt weight (fun x=>-X x) t) X
  let v := fun t=>FiniteTilt.variance s (FiniteTilt.tilt weight (fun x=>-X x) t) X
  let L := fun t=>Real.log (FiniteTilt.total s (FiniteTilt.tilt weight (fun x=>-X x) t))
  have hp (t : ℝ) := FiniteTilt.total_tilt_pos s weight (fun x=>-X x) hw hZ t
  have hd (t : ℝ) : HasDerivAt w (-v t) t := by
    simpa only [w,v,FiniteTilt.covariance_neg_right,FiniteTilt.variance] using
      FiniteTilt.hasDerivAt_mean s weight (fun x=>-X x) X t (ne_of_gt (hp t))
  have hlog (t : ℝ) : HasDerivAt L (-w t) t := by
    have hh := (FiniteTilt.hasDerivAt_total s weight (fun x=>-X x) t).log (ne_of_gt (hp t))
    change HasDerivAt L (FiniteTilt.mean s (FiniteTilt.tilt weight (fun x=>-X x) t) (fun x=>-X x)) t at hh
    simpa only [FiniteTilt.mean_neg,w] using hh
  have hbase : FiniteTilt.tilt weight (fun x=>-X x) 0=weight := by
    funext x; simp [FiniteTilt.tilt]
  have hs : lower 0≤w (time 0) := by simpa only [w,hzero,hbase] using hstart
  have hh := (chain time lower charge DE CE DI CI n hs horder
    (fun _ _ t _=>hd t) (fun _ _ t _=>hlog t) hCE hCI hVE hVI hend hcharge).2
  simpa only [L,hzero,hbase,Real.log_div (ne_of_gt (hp (time n))) (ne_of_gt hZ)] using hh

variable {V : Type*} [DecidableEq V]

/-- Fixed-B graph bridge for the actual conditionally binomial Laplace
transform. The sources must hold on every closed step in the original graph. -/
theorem actual_laplace_chain (G : SimpleGraph V) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B : Set V)) {z : ℝ} (hz : 0<z)
    (time lower charge DE CE DI CI : ℕ → ℝ) (n : ℕ)
    (hzero : time 0=0) (hstart : lower 0≤hardCoreOccupiedMass G S B z)
    (horder : ∀i<n, time i≤time (i+1))
    (hCE : ∀i<n, 0<CE i) (hCI : ∀i<n, 0<CI i)
    (hVE : ∀i<n, ∀t∈Icc (time i) (time (i+1)),
      heterogeneousVariance G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J=>((J∩B).card:ℝ)) ≤ DE i+CE i*
      heterogeneousMean G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J=>((J∩B).card:ℝ)))
    (hVI : ∀i<n, ∀t∈Icc (time i) (time (i+1)),
      heterogeneousVariance G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J=>((J∩B).card:ℝ)) ≤ DI i+CI i*
      heterogeneousMean G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J=>((J∩B).card:ℝ)))
    (hend : ∀i<n, lower (i+1)≤endLower (lower i) (DE i) (CE i) (time (i+1)-time i))
    (hcharge : ∀i<n, charge i ≤ integralLower (lower i) (DI i) (CI i) (time (i+1)-time i)) :
    hardCoreLayerLaplace G S B z (Real.exp (-time n)) ≤ Real.exp (-∑i∈range n, charge i) := by
  let weight := heterogeneousWeight (fun (_:V)=>z)
  let X := fun (J:Finset V)=>((J∩B).card:ℝ)
  have hweight (t : ℝ) : heterogeneousWeight (independentTiltActivities B z (Real.exp (-t))) =
      FiniteTilt.tilt weight (fun J=>-X J) t := by
    funext J; exact independent_tilt_weight_eq B J z t
  have hw : ∀J∈independentSubsets G S, 0≤weight J := by
    intro J _; exact heterogeneousWeight_nonneg (fun _ _=>hz.le)
  have hZ : FiniteTilt.total (independentSubsets G S) weight=partitionFunction G S z := by
    simp only [FiniteTilt.total,weight,heterogeneousWeight,prod_const,partitionFunction]
  have hm : FiniteTilt.mean (independentSubsets G S) weight X=hardCoreOccupiedMass G S B z := by
    rw [hardCoreOccupiedMass_eq_intersection_expectation]
    simp only [FiniteTilt.mean,FiniteTilt.numerator,hZ,weight,X,heterogeneousWeight,prod_const]
    congr 1; apply sum_congr rfl; intro J _; ring
  have hh := finite_log_laplace_chain (independentSubsets G S) weight X hw
    (hZ ▸ partitionFunction_pos G S hz.le) time lower charge DE CE DI CI n hzero
    (hm ▸ hstart) horder hCE hCI
    (fun i hi t ht=>by simpa only [heterogeneousVariance,heterogeneousMean,hweight] using hVE i hi t ht)
    (fun i hi t ht=>by simpa only [heterogeneousVariance,heterogeneousMean,hweight] using hVI i hi t ht)
    hend hcharge
  rw [hZ,←hweight (time n)] at hh
  rw [hardCoreLayerLaplace_eq_heterogeneous_ratio G S B hBS hB hz]
  apply (Real.log_le_iff_le_exp (div_pos _ (partitionFunction_pos G S hz.le))).mp hh
  apply heterogeneousPartition_pos
  intro v _
  unfold independentTiltActivities
  split_ifs <;> positivity

theorem endLower_scale (m L D C duration : ℝ) :
    endLower (m*L) (m*D) C duration=m*endLower L D C duration := by
  unfold endLower; ring

theorem integralLower_scale (m L D C duration : ℝ) :
    integralLower (m*L) (m*D) C duration=m*integralLower L D C duration := by
  unfold integralLower; ring

/-- Certificate-friendly normalization, with one original mean m for all
steps. Rationally certified endpoint and area prices are independent. -/
theorem actual_laplace_chain_scaled (G : SimpleGraph V) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B : Set V)) {z m retention : ℝ}
    (hz : 0<z) (hm : 0≤m)
    (time lower charge DE CE DI CI : ℕ → ℝ) (n : ℕ)
    (hzero : time 0=0) (hstart : m*lower 0≤hardCoreOccupiedMass G S B z)
    (horder : ∀i<n, time i≤time (i+1))
    (hCE : ∀i<n, 0<CE i) (hCI : ∀i<n, 0<CI i)
    (hVE : ∀i<n, ∀t∈Icc (time i) (time (i+1)),
      heterogeneousVariance G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J=>((J∩B).card:ℝ)) ≤ m*DE i+CE i*
      heterogeneousMean G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J=>((J∩B).card:ℝ)))
    (hVI : ∀i<n, ∀t∈Icc (time i) (time (i+1)),
      heterogeneousVariance G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J=>((J∩B).card:ℝ)) ≤ m*DI i+CI i*
      heterogeneousMean G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J=>((J∩B).card:ℝ)))
    (hend : ∀i<n, lower (i+1)≤endLower (lower i) (DE i) (CE i) (time (i+1)-time i))
    (hcharge : ∀i<n, charge i ≤ integralLower (lower i) (DI i) (CI i) (time (i+1)-time i))
    (hrt : 0≤retention) (htime : retention≤Real.exp (-time n)) :
    hardCoreLayerLaplace G S B z retention ≤ Real.exp (-m*∑i∈range n, charge i) := by
  have hh := actual_laplace_chain G S B hBS hB hz time (fun i=>m*lower i)
    (fun i=>m*charge i) (fun i=>m*DE i) CE (fun i=>m*DI i) CI n hzero hstart
    horder hCE hCI hVE hVI
    (fun i hi=>by rw [endLower_scale]; exact mul_le_mul_of_nonneg_left (hend i hi) hm)
    (fun i hi=>by rw [integralLower_scale]; exact mul_le_mul_of_nonneg_left (hcharge i hi) hm)
  have hmono := hardCoreLayerLaplace_mono G S B hz.le hrt htime
  apply hmono.trans
  simpa only [←mul_sum,neg_mul] using hh

#print axioms actual_laplace_chain_scaled
#print axioms finite_log_laplace_chain
#print axioms actual_laplace_chain
#print axioms endpoint_upper
#print axioms whole_step_upper
#print axioms affine_endpoint
#print axioms affine_log_step
#print axioms chain
end ForestUnimodality.PiecewiseFlowLaplace
