import ForestUnimodality.LogisticTilt

/-! The finite-tilt quadratic correction in the original available-count
law. All moments and tail exponents retain the same original mean m. -/
namespace ForestUnimodality
open Set
variable {V : Type*} [DecidableEq V]

theorem hardCoreAvailableLowerTail_le_corrected_constant
    (G : SimpleGraph V) (S B : Finset V) (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V))
    {z u D threshold v : ℝ} (hz : 0<z) (hu : 0≤u) (ht : 0≤threshold)
    (hsource : ∀t∈Icc 0 u,
      heterogeneousVariance G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J=>((J∩B).card:ℝ))≤D)
    (hpath : ∀t∈Icc 0 u, v≤logisticTilt z t*(1-logisticTilt z t)) :
    hardCoreAvailableLowerTail G S B z threshold≤
      Real.exp (threshold*(z/(1+z))*u-hardCoreOccupiedMass G S B z*u+(D-threshold*v)*u^2/2) := by
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
  have hl := logisticLogLaplace_quadratic_lower hz hu hpath
  rw [logisticLogLaplace_eq hz] at hl
  have hlt := mul_le_mul_of_nonneg_left hl ht
  nlinarith

theorem hardCoreAvailableLowerTail_le_corrected_rate
    (G : SimpleGraph V) (S B : Finset V) (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V))
    {z u C α v qa rate : ℝ} (hz : 0<z) (hu : 0≤u) (hα0 : 0≤α) (hα1 : α≤1)
    (hqa : qa≤z/(1+z))
    (hsource : ∀t∈Icc 0 u,
      heterogeneousVariance G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J=>((J∩B).card:ℝ))≤C*hardCoreAvailableMean G S B z)
    (hpath : ∀t∈Icc 0 u, v≤logisticTilt z t*(1-logisticTilt z t))
    (hrate : rate≤qa*(1-α)*u-(C-α*v)*u^2/2) :
    hardCoreAvailableLowerTail G S B z (α*hardCoreAvailableMean G S B z)≤
      Real.exp (-rate*hardCoreAvailableMean G S B z) := by
  have hm := hardCoreAvailableMean_nonneg G S B hz.le
  have h := hardCoreAvailableLowerTail_le_corrected_constant G S B hBS hB hz hu
    (mul_nonneg hα0 hm) hsource hpath
  rw [hardCoreOccupiedMass_eq_activity_available_mean G S B hBS hB hz] at h
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hqu := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hqa (sub_nonneg.mpr hα1)) hu
  have hrate' : rate≤(z/(1+z))*(1-α)*u-(C-α*v)*u^2/2 := by linarith
  have hh := mul_le_mul_of_nonneg_right hrate' hm
  nlinarith

/-- Endpoint variance and an exponential bound certify all intermediate
tilt activities on [0,U], then a single rational rate certifies the tail. -/
theorem hardCoreAvailableLowerTail_le_endpoint_corrected_rate
    (G : SimpleGraph V) (S B : Finset V) (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V))
    {z u U E lo hi C α v qa rate : ℝ} (hz : 0<z) (hu : 0≤u) (huU : u≤U)
    (hE : 0<E) (hexp : Real.exp U≤E) (hlo : lo≤z/(E+z)) (hhi : z/(1+z)≤hi)
    (hvlo : v≤lo*(1-lo)) (hvhi : v≤hi*(1-hi))
    (hα0 : 0≤α) (hα1 : α≤1) (hqa : qa≤z/(1+z))
    (hsource : ∀t∈Icc 0 u,
      heterogeneousVariance G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J=>((J∩B).card:ℝ))≤C*hardCoreAvailableMean G S B z)
    (hrate : rate≤qa*(1-α)*u-(C-α*v)*u^2/2) :
    hardCoreAvailableLowerTail G S B z (α*hardCoreAvailableMean G S B z)≤
      Real.exp (-rate*hardCoreAvailableMean G S B z) := by
  apply hardCoreAvailableLowerTail_le_corrected_rate G S B hBS hB hz hu hα0 hα1 hqa hsource ?_ hrate
  intro t ht
  have hl := (hlo.trans (logisticTilt_endpoint_lower hz hE hexp)).trans
    (logisticTilt_antitone hz (ht.2.trans huU))
  have hh : logisticTilt z t≤hi := by
    have hm := logisticTilt_antitone hz ht.1
    simp only [logisticTilt,neg_zero,Real.exp_zero,mul_one] at hm
    exact hm.trans hhi
  exact (le_min hvlo hvhi).trans (bernoulli_variance_ge_min hl hh)

theorem exp_half_le_33_20 : Real.exp (1/2:ℝ)≤33/20 := by
  have hc : ExpEnclosure.smallCheck (1/2) 12 1 (33/20)=true := by decide +kernel
  have hh := (ExpEnclosure.smallCheck_sound hc).2
  norm_num at hh ⊢
  exact hh

#print axioms hardCoreAvailableLowerTail_le_endpoint_corrected_rate
#print axioms exp_half_le_33_20
end ForestUnimodality
