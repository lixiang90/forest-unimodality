import ForestUnimodality.PiecewiseFlowLaplace

/-! The zero-slope uniform variance source has a polynomial comparison formula.
This module includes that genuine boundary case in the actual fixed-B chain. -/
namespace ForestUnimodality.PiecewiseFlowZeroSlope
open Set Finset

theorem uniform_endpoint {w v : ℝ → ℝ} {a b L D : ℝ} (hab : a≤b)
    (hd : ∀t∈Icc a b, HasDerivAt w (-v t) t)
    (hv : ∀t∈Icc a b, v t≤D) (hL : L≤w a) :
    L-D*(b-a)≤w b := by
  have hh := PiecewiseFlowLaplace.endpoint_upper hab
    (f:=fun t=>-w t) (df:=v) (U := -L) (d:=D)
    (fun t ht=>by convert (hd t ht).neg using 1 <;> first | rfl | simp only [neg_neg]) hv (by linarith)
  linarith

theorem uniform_log_step {w v logZ : ℝ → ℝ} {a b L D : ℝ} (hab : a≤b)
    (hd : ∀t∈Icc a b, HasDerivAt w (-v t) t)
    (hlog : ∀t∈Icc a b, HasDerivAt logZ (-w t) t)
    (hv : ∀t∈Icc a b, v t≤D) (hL : L≤w a) :
    logZ b-logZ a≤-(L*(b-a)-D*(b-a)^2/2) := by
  let g := fun t=>logZ t+L*(t-a)-D/2*(t-a)^2
  have hg (t:ℝ) (ht:t∈Icc a b) : HasDerivAt g (-w t+L-D*(t-a)) t := by
    convert ((hlog t ht).add (((hasDerivAt_id t).sub_const a).const_mul L)).sub
      ((((hasDerivAt_id t).sub_const a).pow 2).const_mul (D/2)) using 1 <;> first | rfl | (simp only [neg_neg]) | (try simp only [id_eq]; ring)
  have hdf (t:ℝ) (ht:t∈Icc a b) : -w t+L-D*(t-a)≤0 := by
    have hh := uniform_endpoint ht.1 (fun x hx=>hd x ⟨hx.1,hx.2.trans ht.2⟩)
      (fun x hx=>hv x ⟨hx.1,hx.2.trans ht.2⟩) hL
    linarith
  have hh := PiecewiseFlowLaplace.endpoint_upper hab hg hdf (le_refl (g a))
  dsimp [g] at hh
  nlinarith

noncomputable def endLower (L D C duration : ℝ) : ℝ :=
  if C=0 then L-D*duration else PiecewiseFlowLaplace.endLower L D C duration
noncomputable def integralLower (L D C duration : ℝ) : ℝ :=
  if C=0 then L*duration-D*duration^2/2 else PiecewiseFlowLaplace.integralLower L D C duration

theorem affine_endpoint {w v : ℝ → ℝ} {a b L D C : ℝ} (hab : a≤b)
    (hC : 0≤C) (hd : ∀t∈Icc a b, HasDerivAt w (-v t) t)
    (hv : ∀t∈Icc a b, v t≤D+C*w t) (hL : L≤w a) :
    endLower L D C (b-a)≤w b := by
  by_cases hc : C=0
  · simp only [endLower,hc,if_true]
    exact uniform_endpoint hab hd (by simpa only [hc,zero_mul,add_zero] using hv) hL
  · simp only [endLower,hc,if_false]
    exact PiecewiseFlowLaplace.affine_endpoint hab (lt_of_le_of_ne hC (Ne.symm hc)) hd hv hL

theorem affine_log_step {w v logZ : ℝ → ℝ} {a b L D C : ℝ} (hab : a≤b)
    (hC : 0≤C) (hd : ∀t∈Icc a b, HasDerivAt w (-v t) t)
    (hlog : ∀t∈Icc a b, HasDerivAt logZ (-w t) t)
    (hv : ∀t∈Icc a b, v t≤D+C*w t) (hL : L≤w a) :
    logZ b-logZ a≤-integralLower L D C (b-a) := by
  by_cases hc : C=0
  · simp only [integralLower,hc,if_true]
    exact uniform_log_step hab hd hlog (by simpa only [hc,zero_mul,add_zero] using hv) hL
  · simp only [integralLower,hc,if_false]
    exact PiecewiseFlowLaplace.affine_log_step hab (lt_of_le_of_ne hC (Ne.symm hc)) hd hlog hv hL

/-- All values denote bounds on the same actual w and logZ. In particular the
endpoint and integral certificates may choose different affine sources. -/
theorem chain {w v logZ : ℝ → ℝ} (time lower charge DE CE DI CI : ℕ → ℝ)
    (n : ℕ) (hstart : lower 0≤w (time 0))
    (horder : ∀i<n, time i≤time (i+1))
    (hd : ∀i<n, ∀t∈Icc (time i) (time (i+1)), HasDerivAt w (-v t) t)
    (hlog : ∀i<n, ∀t∈Icc (time i) (time (i+1)), HasDerivAt logZ (-w t) t)
    (hCE : ∀i<n, 0≤CE i) (hCI : ∀i<n, 0≤CI i)
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
    (hCE : ∀i<n, 0≤CE i) (hCI : ∀i<n, 0≤CI i)
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
    (hCE : ∀i<n, 0≤CE i) (hCI : ∀i<n, 0≤CI i)
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
  by_cases hC : C=0
  · simp only [endLower,hC,if_true]; ring
  · simp only [endLower,hC,if_false]; exact PiecewiseFlowLaplace.endLower_scale m L D C duration

theorem integralLower_scale (m L D C duration : ℝ) :
    integralLower (m*L) (m*D) C duration=m*integralLower L D C duration := by
  by_cases hC : C=0
  · simp only [integralLower,hC,if_true]; ring
  · simp only [integralLower,hC,if_false]; exact PiecewiseFlowLaplace.integralLower_scale m L D C duration

/-- Certificate-friendly normalization, with one original mean m for all
steps. Rationally certified endpoint and area prices are independent. -/
theorem actual_laplace_chain_scaled (G : SimpleGraph V) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B : Set V)) {z m retention : ℝ}
    (hz : 0<z) (hm : 0≤m)
    (time lower charge DE CE DI CI : ℕ → ℝ) (n : ℕ)
    (hzero : time 0=0) (hstart : m*lower 0≤hardCoreOccupiedMass G S B z)
    (horder : ∀i<n, time i≤time (i+1))
    (hCE : ∀i<n, 0≤CE i) (hCI : ∀i<n, 0≤CI i)
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

/-- All values denote bounds on the same actual w and logZ. In particular the
endpoint and integral certificates may choose different affine sources. -/
theorem chain_clamped {w v logZ : ℝ → ℝ} (time lower charge DE CE DI CI : ℕ → ℝ)
    (n : ℕ) (hstart : lower 0≤w (time 0)) (hnonneg : ∀t, 0≤w t)
    (horder : ∀i<n, time i≤time (i+1))
    (hd : ∀i<n, ∀t∈Icc (time i) (time (i+1)), HasDerivAt w (-v t) t)
    (hlog : ∀i<n, ∀t∈Icc (time i) (time (i+1)), HasDerivAt logZ (-w t) t)
    (hCE : ∀i<n, 0≤CE i) (hCI : ∀i<n, 0≤CI i)
    (hVE : ∀i<n, ∀t∈Icc (time i) (time (i+1)), v t≤DE i+CE i*w t)
    (hVI : ∀i<n, ∀t∈Icc (time i) (time (i+1)), v t≤DI i+CI i*w t)
    (hend : ∀i<n, lower (i+1)≤max 0 (endLower (lower i) (DE i) (CE i) (time (i+1)-time i)))
    (hcharge : ∀i<n, charge i ≤ max 0 (integralLower (lower i) (DI i) (CI i) (time (i+1)-time i))) :
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
    have he' := max_le (hnonneg (time (n+1))) he
    have hz := PiecewiseFlowLaplace.endpoint_upper (horder n (by omega))
      (hlog n (by omega)) (fun t _=>neg_nonpos.mpr (hnonneg t)) (le_refl (logZ (time n)))
    have hl' : logZ (time (n+1))-logZ (time n)≤
        -max 0 (integralLower (lower n) (DI n) (CI n) (time (n+1)-time n)) := by
      rcases le_total 0 (integralLower (lower n) (DI n) (CI n) (time (n+1)-time n)) with hh | hh
      · rw [max_eq_right hh]; exact hl
      · rw [max_eq_left hh,neg_zero]; linarith
    constructor
    · exact (hend n (by omega)).trans he' 
    · rw [sum_range_succ]
      have hc := hcharge n (by omega)
      linarith [hh.2,hl']

/-- Specialization to the actual finite exponential family. Only affine
variance sources remain premises; neither an ODE trajectory nor a Laplace
bound is assumed. The mark X is fixed for the entire chain. -/
theorem finite_log_laplace_chain_clamped {α : Type*} (s : Finset α) (weight X : α → ℝ)
    (hw : ∀x∈s, 0≤weight x) (hX : ∀x∈s, 0≤X x) (hZ : 0<FiniteTilt.total s weight)
    (time lower charge DE CE DI CI : ℕ → ℝ) (n : ℕ)
    (hzero : time 0=0) (hstart : lower 0≤FiniteTilt.mean s weight X)
    (horder : ∀i<n, time i≤time (i+1))
    (hCE : ∀i<n, 0≤CE i) (hCI : ∀i<n, 0≤CI i)
    (hVE : ∀i<n, ∀t∈Icc (time i) (time (i+1)),
      FiniteTilt.variance s (FiniteTilt.tilt weight (fun x=>-X x) t) X ≤
        DE i+CE i*FiniteTilt.mean s (FiniteTilt.tilt weight (fun x=>-X x) t) X)
    (hVI : ∀i<n, ∀t∈Icc (time i) (time (i+1)),
      FiniteTilt.variance s (FiniteTilt.tilt weight (fun x=>-X x) t) X ≤
        DI i+CI i*FiniteTilt.mean s (FiniteTilt.tilt weight (fun x=>-X x) t) X)
    (hend : ∀i<n, lower (i+1)≤max 0 (endLower (lower i) (DE i) (CE i) (time (i+1)-time i)))
    (hcharge : ∀i<n, charge i ≤ max 0 (integralLower (lower i) (DI i) (CI i) (time (i+1)-time i))) :
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
  have hnonneg (t:ℝ) : 0≤w t := by
    apply div_nonneg _ (hp t).le
    apply sum_nonneg
    intro x hx
    exact mul_nonneg (mul_nonneg (hw x hx) (Real.exp_pos _).le) (hX x hx)
  have hh := (chain_clamped time lower charge DE CE DI CI n hs hnonneg horder
    (fun _ _ t _=>hd t) (fun _ _ t _=>hlog t) hCE hCI hVE hVI hend hcharge).2
  simpa only [L,hzero,hbase,Real.log_div (ne_of_gt (hp (time n))) (ne_of_gt hZ)] using hh


/-- Fixed-B graph bridge for the actual conditionally binomial Laplace
transform. The sources must hold on every closed step in the original graph. -/
theorem actual_laplace_chain_clamped (G : SimpleGraph V) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B : Set V)) {z : ℝ} (hz : 0<z)
    (time lower charge DE CE DI CI : ℕ → ℝ) (n : ℕ)
    (hzero : time 0=0) (hstart : lower 0≤hardCoreOccupiedMass G S B z)
    (horder : ∀i<n, time i≤time (i+1))
    (hCE : ∀i<n, 0≤CE i) (hCI : ∀i<n, 0≤CI i)
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
    (hend : ∀i<n, lower (i+1)≤max 0 (endLower (lower i) (DE i) (CE i) (time (i+1)-time i)))
    (hcharge : ∀i<n, charge i ≤ max 0 (integralLower (lower i) (DI i) (CI i) (time (i+1)-time i))) :
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
  have hh := finite_log_laplace_chain_clamped (independentSubsets G S) weight X hw (fun _ _=>Nat.cast_nonneg _)
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

theorem max_zero_mul {m : ℝ} (hm : 0≤m) (x : ℝ) : max 0 (m*x)=m*max 0 x := by
  by_cases hx : 0≤x
  · rw [max_eq_right hx,max_eq_right (mul_nonneg hm hx)]
  · rw [max_eq_left (le_of_not_ge hx),max_eq_left (mul_nonpos_of_nonneg_of_nonpos hm (le_of_not_ge hx)),mul_zero]

/-- Certificate-friendly normalization, with one original mean m for all
steps. Rationally certified endpoint and area prices are independent. -/
theorem actual_laplace_chain_scaled_clamped (G : SimpleGraph V) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B : Set V)) {z m retention : ℝ}
    (hz : 0<z) (hm : 0≤m)
    (time lower charge DE CE DI CI : ℕ → ℝ) (n : ℕ)
    (hzero : time 0=0) (hstart : m*lower 0≤hardCoreOccupiedMass G S B z)
    (horder : ∀i<n, time i≤time (i+1))
    (hCE : ∀i<n, 0≤CE i) (hCI : ∀i<n, 0≤CI i)
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
    (hend : ∀i<n, lower (i+1)≤max 0 (endLower (lower i) (DE i) (CE i) (time (i+1)-time i)))
    (hcharge : ∀i<n, charge i ≤ max 0 (integralLower (lower i) (DI i) (CI i) (time (i+1)-time i)))
    (hrt : 0≤retention) (htime : retention≤Real.exp (-time n)) :
    hardCoreLayerLaplace G S B z retention ≤ Real.exp (-m*∑i∈range n, charge i) := by
  have hh := actual_laplace_chain_clamped G S B hBS hB hz time (fun i=>m*lower i)
    (fun i=>m*charge i) (fun i=>m*DE i) CE (fun i=>m*DI i) CI n hzero hstart
    horder hCE hCI hVE hVI
    (fun i hi=>by rw [endLower_scale,max_zero_mul hm]; exact mul_le_mul_of_nonneg_left (hend i hi) hm)
    (fun i hi=>by rw [integralLower_scale,max_zero_mul hm]; exact mul_le_mul_of_nonneg_left (hcharge i hi) hm)
  have hmono := hardCoreLayerLaplace_mono G S B hz.le hrt htime
  apply hmono.trans
  simpa only [←mul_sum,neg_mul] using hh

#print axioms actual_laplace_chain_scaled_clamped
#print axioms actual_laplace_chain_clamped
#print axioms uniform_endpoint
#print axioms uniform_log_step
#print axioms affine_endpoint
#print axioms affine_log_step
#print axioms actual_laplace_chain_scaled
end ForestUnimodality.PiecewiseFlowZeroSlope
