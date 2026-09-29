import ForestUnimodality.FixedIndependentTilt
import ForestUnimodality.SourceMixtureCertificate

/-! Sound whole-step and endpoint bounds for the genuine fixed-independent-set
flow. All source validity domains cover the complete closed step. -/
namespace ForestUnimodality.FixedIndependentTilt
open Finset Set
variable {V : Type*} [DecidableEq V]

theorem markedMean_nonneg (G : SimpleGraph V) (S B : Finset V) {z : ℝ} (hz : 0<z) (t : ℝ) :
    0≤markedMean G S B z t := by
  apply div_nonneg _ (tilted_total_pos G S B hz t).le
  apply sum_nonneg
  intro K _
  unfold weight inside
  positivity

theorem markedMean_antitone (G : SimpleGraph V) (S B : Finset V) {z : ℝ} (hz : 0<z) :
    Antitone (markedMean G S B z) := by
  apply antitone_of_deriv_nonpos (fun t=>(hasDerivAt_markedMean G S B hz t).differentiableAt)
  intro t
  rw [(hasDerivAt_markedMean G S B hz t).deriv]
  apply neg_nonpos.mpr
  apply finite_variance_nonneg _ _ _ _ (tilted_total_pos G S B hz t)
  intro K _
  unfold weight
  positivity

theorem markedMean_zero (G : SimpleGraph V) (S B : Finset V) (z : ℝ) :
    markedMean G S B z 0=hardCoreOccupiedMass G S B z := by
  unfold markedMean
  rw [weight_eq_tilt]
  have hh : FiniteTilt.tilt (heterogeneousWeight (fun (_:V)=>z)) (fun K=>-inside B K) 0=
      heterogeneousWeight (fun (_:V)=>z) := by funext K; simp [FiniteTilt.tilt]
  rw [hh]
  exact heterogeneousMean_common_intersection G S B z

/-- The denominator m is the original available mean, not the current one. -/
theorem markedMean_le_initial_available (G : SimpleGraph V) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V)) {z t : ℝ} (hz : 0<z) (ht : 0≤t) :
    markedMean G S B z t ≤ logisticTilt z t*hardCoreAvailableMean G S B z := by
  have hh := markedMean_div_logistic_antitone G S B hBS hB hz ht
  dsimp only at hh
  rw [markedMean_zero,hardCoreOccupiedMass_eq_activity_available_mean G S B hBS hB hz] at hh
  have hq : logisticTilt z 0=z/(1+z) := by simp [logisticTilt]
  rw [hq,mul_div_cancel_left₀ _ (ne_of_gt (by positivity : 0<z/(1+z)))] at hh
  exact (div_le_iff₀ (logisticTilt_pos hz t)).mp hh |>.trans_eq (mul_comm _ _)

/-- Actual signed drift from a whole-step complement-variance cap and an
endpoint occupation floor. Monotonicity of w transports the endpoint floor
backward to every point of the closed step. -/
theorem signed_drift_bound (G : SimpleGraph V) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V)) {z a b m L Vc qu : ℝ}
    (hz : 0<z) (hm : 0≤m) (hL : 0≤L) (_hqu : qu≤1)
    (hend : m*L≤markedMean G S B z b)
    (hq : ∀t∈Icc a b, logisticTilt z t≤qu)
    (hv : ∀t∈Icc a b, complementVariance G S B z t≤m*Vc) :
    ∀t∈Icc a b, deriv (totalMean G S B z) t≤m*(Vc/4-(1-qu)*L) := by
  intro t ht
  have hlo := hend.trans (markedMean_antitone G S B hz ht.2)
  have hprod := mul_le_mul (show 1-qu≤1-logisticTilt z t by linarith [hq t ht]) hlo
    (mul_nonneg hm hL) (sub_nonneg.mpr (logisticTilt_lt_one hz t).le)
  have hd := totalMean_derivative_upper G S B hBS hB hz t
  nlinarith [hv t ht]

/-- The two bounds have distinct roles when the certified drift is negative. -/
theorem totalMean_step_bounds (G : SimpleGraph V) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V)) {z a b m L U Vc qu : ℝ}
    (hz : 0<z) (hab : a≤b) (hm : 0≤m) (hL : 0≤L) (hqu : qu≤1)
    (hstart : totalMean G S B z a≤m*U) (hend : m*L≤markedMean G S B z b)
    (hq : ∀t∈Icc a b, logisticTilt z t≤qu)
    (hv : ∀t∈Icc a b, complementVariance G S B z t≤m*Vc) :
    totalMean G S B z b ≤ m*(U+(Vc/4-(1-qu)*L)*(b-a)) ∧
    ∀t∈Icc a b, totalMean G S B z t ≤ m*(U+max 0 (Vc/4-(1-qu)*L)*(b-a)) := by
  have hd (t : ℝ) : HasDerivAt (totalMean G S B z) (deriv (totalMean G S B z) t) t :=
    (hasDerivAt_totalMean G S B hz t).differentiableAt.hasDerivAt
  have hdle := signed_drift_bound G S B hBS hB hz hm hL hqu hend hq hv
  have he := PiecewiseFlowLaplace.endpoint_upper hab (fun t _=>hd t) hdle hstart
  have hs := PiecewiseFlowLaplace.whole_step_upper hab (fun t _=>hd t) hdle hstart
  constructor
  · nlinarith
  · intro t ht
    have hh := hs t ht
    have hmmax : max 0 (m*(Vc/4-(1-qu)*L))=m*max 0 (Vc/4-(1-qu)*L) := by
      by_cases hp : 0≤Vc/4-(1-qu)*L
      · rw [max_eq_right hp,max_eq_right (mul_nonneg hm hp)]
      · rw [max_eq_left (le_of_not_ge hp),max_eq_left (mul_nonpos_of_nonneg_of_nonpos hm (le_of_not_ge hp)),mul_zero]
    rw [hmmax] at hh
    nlinarith

/-- Every vertex activity is inside a source domain for the entire step.
In particular the complement keeps the original upper bound b. -/
theorem closed_step_activities (B : Finset V) {z a b start finish lower upper : ℝ}
    (ha : 0<a) (hzlo : a≤z) (hzhi : z≤b) (hstart : 0≤start)
    (hlo : lower≤a*Real.exp (-finish)) (hhi : b≤upper) :
    ∀t∈Icc start finish, ∀v,
      lower ≤ independentTiltActivities B z (Real.exp (-t)) v ∧
      independentTiltActivities B z (Real.exp (-t)) v≤upper := by
  intro t ht v
  have hehi : Real.exp (-t)≤1 := Real.exp_le_one_iff.mpr (by linarith [ht.1])
  have helo : Real.exp (-finish)≤Real.exp (-t) := Real.exp_le_exp.mpr (by linarith [ht.2])
  have hz : 0≤z := (ha.trans_le hzlo).le
  have hlo' : lower≤z*Real.exp (-t) := hlo.trans (mul_le_mul hzlo helo (Real.exp_pos _).le hz)
  have hhi' : z*Real.exp (-t)≤upper := (mul_le_of_le_one_right hz hehi).trans (hzhi.trans hhi)
  have hlz : lower≤z := hlo'.trans (mul_le_of_le_one_right hz hehi)
  unfold independentTiltActivities
  split_ifs
  · simpa only [mul_comm] using And.intro hlo' hhi'
  · exact ⟨hlz,hzhi.trans hhi⟩

/-- A valid marked source becomes an affine ODE penalty only after a safe
whole-step total-mean cap has been proved. -/
theorem marked_source_on_step (G : SimpleGraph V) (hG : G.IsAcyclic) (S B : Finset V)
    (hB : G.IsIndepSet (B:Set V)) {z a b start finish lower upper m U : ℝ}
    (ha : 0<a) (hzlo : a≤z) (hzhi : z≤b) (hstart : 0≤start)
    (hlower : 0<lower) (hlo : lower≤a*Real.exp (-finish)) (hhi : b≤upper)
    (P : SourceRowParameters) (hP : P.Admissible) (hPA : 0≤P.A)
    (hvalid : SourceRowValid P lower upper)
    (hmu : ∀t∈Icc start finish, totalMean G S B z t≤m*U) :
    ∀t∈Icc start finish, markedVariance G S B z t≤m*(P.A*U)+P.C*markedMean G S B z t := by
  intro t ht
  have hh := forest_independent_count_variance_of_scalar_certificate G hG S B hB
    (independentTiltActivities B z (Real.exp (-t))) hlower
    (fun v _=>closed_step_activities B ha hzlo hzhi hstart hlo hhi t ht v) P hP hvalid
  have hbound := mul_le_mul_of_nonneg_left (hmu t ht) hPA
  change markedVariance G S B z t≤_ at ⊢
  simp only [markedVariance,markedMean,totalMean,weight_eq_heterogeneous,
    heterogeneousVariance,heterogeneousMean] at hh hbound ⊢
  unfold inside
  nlinarith

theorem finite_variance_congr {α : Type*} (s : Finset α) (w X Y : α → ℝ)
    (he : ∀x∈s, X x=Y x) : FiniteTilt.variance s w X=FiniteTilt.variance s w Y := by
  rw [FiniteTilt.variance_eq_second_sub_mean_sq,FiniteTilt.variance_eq_second_sub_mean_sq,
    FiniteTilt.mean_congr s w X Y he,FiniteTilt.mean_congr s w (fun x=>X x^2)
      (fun x=>Y x^2) (fun x hx=>by rw [he x hx])]

theorem complement_mean_eq (G : SimpleGraph V) (S B : Finset V) (z t : ℝ) :
    FiniteTilt.mean (independentSubsets G S) (weight B z (z*Real.exp (-t))) (outside B)=
      totalMean G S B z t-markedMean G S B z t := by
  unfold totalMean markedMean
  rw [←FiniteTilt.mean_sub]
  apply FiniteTilt.mean_congr
  intro K _
  have hh := split_card K B
  unfold inside outside
  have he : (K.card:ℝ)=((K\B).card:ℝ)+((K∩B).card:ℝ) := by exact_mod_cast hh
  linarith

/-- The complement need not be independent. The generic affine source
supports its indicator and is applied to the current original-B tilt. -/
theorem complement_affine_source (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S B : Finset V) {z b t : ℝ} (hz : 0<z) (hzb : z≤b) (ht : 0≤t)
    (P : AffineSourceParameters) (hP : P.Admissible) (hvalid : AffineSourceRowValid P b) :
    complementVariance G S B z t ≤ P.A*((S\B).card:ℝ)+
      P.C*(totalMean G S B z t-markedMean G S B z t) := by
  have ha : ∀v∈S, 0 < independentTiltActivities B z (Real.exp (-t)) v ∧
      independentTiltActivities B z (Real.exp (-t)) v≤b := by
    intro v _
    have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
    unfold independentTiltActivities
    split_ifs
    · exact ⟨mul_pos (Real.exp_pos _) hz,(by nlinarith : Real.exp (-t)*z≤z).trans hzb⟩
    · exact ⟨hz,hzb⟩
  have hh := forest_marked_affine_source_variance G hG S (S\B) sdiff_subset
    (independentTiltActivities B z (Real.exp (-t))) ha P hP hvalid
  have he : ∀K∈independentSubsets G S, ((K∩(S\B)).card:ℝ)=outside B K := by
    intro K hK
    have hs : K∩(S\B)=K\B := by
      ext v
      simp only [Finset.mem_inter,Finset.mem_sdiff]
      exact ⟨fun h=>⟨h.1,h.2.2⟩,fun h=>⟨h.1,(mem_independentSubsets.mp hK).1 h.1,h.2⟩⟩
    rw [hs]; rfl
  simp only [heterogeneousVariance,heterogeneousMean,←weight_eq_heterogeneous] at hh
  rw [finite_variance_congr _ _ _ _ he,FiniteTilt.mean_congr _ _ _ _ he,
    complement_mean_eq] at hh
  exact hh

theorem complement_affine_cap (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S B : Finset V) {z b a finish m beta U L : ℝ}
    (hz : 0<z) (hzb : z≤b) (ha : 0≤a) (hm : 0≤m)
    (P : AffineSourceParameters) (hP : P.Admissible) (hvalid : AffineSourceRowValid P b)
    (hA : 0≤P.A) (hC : 0≤P.C) (hcard : ((S\B).card:ℝ)≤m*beta)
    (hmu : ∀t∈Icc a finish, totalMean G S B z t≤m*U)
    (hend : m*L≤markedMean G S B z finish) :
    ∀t∈Icc a finish, complementVariance G S B z t≤m*(P.A*beta+P.C*max 0 (U-L)) := by
  intro t ht
  have hh := complement_affine_source G hG S B hz hzb (ha.trans ht.1) P hP hvalid
  have hw := hend.trans (markedMean_antitone G S B hz ht.2)
  have hdiff : totalMean G S B z t-markedMean G S B z t≤m*max 0 (U-L) := by
    have hp := mul_le_mul_of_nonneg_left (le_max_right 0 (U-L)) hm
    nlinarith [hmu t ht]
  have h₁ := mul_le_mul_of_nonneg_left hcard hA
  have h₂ := mul_le_mul_of_nonneg_left hdiff hC
  nlinarith

/-- Cauchy supplies the coarse total-mean growth bound from actual variances;
no monotonicity of the total mean is required. -/
theorem totalMean_cauchy_drift (G : SimpleGraph V) (S B : Finset V)
    {z t m VB VK : ℝ} (hz : 0<z) (hm : 0≤m) (hVB : 0≤VB) (hVK : 0≤VK)
    (hb : markedVariance G S B z t≤m*VB)
    (hk : FiniteTilt.variance (independentSubsets G S) (weight B z (z*Real.exp (-t)))
      (fun K=>(K.card:ℝ))≤m*VK) :
    deriv (totalMean G S B z) t ≤ m*Real.sqrt (VB*VK) := by
  let w := weight B z (z*Real.exp (-t))
  have hw : ∀K∈independentSubsets G S, 0≤w K := by intro K _; unfold w weight; positivity
  have hp := tilted_total_pos G S B hz t
  have hv := finite_variance_nonneg (independentSubsets G S) w (inside B) hw hp
  have hcov := FiniteTilt.covariance_sq_le_variance_mul_variance (independentSubsets G S) w
    (fun K=>(K.card:ℝ)) (inside B) hw hp
  have hprod := mul_le_mul hk hb hv (mul_nonneg hm hVK)
  have hs := Real.sq_sqrt (mul_nonneg hVB hVK)
  have hpos := mul_nonneg hm (Real.sqrt_nonneg (VB*VK))
  rw [(hasDerivAt_totalMean G S B hz t).deriv]
  change _ ≤ m*Real.sqrt (VB*VK)
  dsimp only [w,markedVariance] at hcov hprod
  have hs' : (m*Real.sqrt (VB*VK))^2=m*VK*(m*VB) := by rw [mul_pow,hs]; ring
  nlinarith [sq_nonneg (m*Real.sqrt (VB*VK)+FiniteTilt.covariance (independentSubsets G S)
    (weight B z (z*Real.exp (-t))) (fun K=>(K.card:ℝ)) (inside B))]

#print axioms complement_affine_source
#print axioms complement_affine_cap
#print axioms totalMean_cauchy_drift
#print axioms markedMean_le_initial_available
#print axioms totalMean_step_bounds
#print axioms closed_step_activities
#print axioms marked_source_on_step
end ForestUnimodality.FixedIndependentTilt
