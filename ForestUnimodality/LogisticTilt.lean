import ForestUnimodality.ConstantSourceLaplace

/-! Exact Bernoulli tilt curvature and its finite-path quadratic correction.
This retains the original q in the linear term throughout. -/
namespace ForestUnimodality
open Set

noncomputable def logisticTilt (z t : ℝ) : ℝ := z*Real.exp (-t)/(1+z*Real.exp (-t))
noncomputable def logisticLogLaplace (z t : ℝ) : ℝ :=
  Real.log (1+z*Real.exp (-t))-Real.log (1+z)

theorem logisticTilt_pos {z : ℝ} (hz : 0<z) (t : ℝ) : 0<logisticTilt z t := by
  unfold logisticTilt
  positivity

theorem logisticTilt_lt_one {z : ℝ} (hz : 0<z) (t : ℝ) : logisticTilt z t<1 := by
  unfold logisticTilt
  exact (div_lt_one (by positivity)).mpr (by linarith)

theorem hasDerivAt_logisticTilt {z : ℝ} (hz : 0<z) (t : ℝ) :
    HasDerivAt (logisticTilt z) (-(logisticTilt z t*(1-logisticTilt z t))) t := by
  have hd : HasDerivAt (fun s : ℝ=>z*Real.exp (-s)) (-z*Real.exp (-t)) t := by
    convert (((hasDerivAt_id t).neg.exp).const_mul z) using 1
    all_goals first | rfl | (change -z*Real.exp (-t)=z*(Real.exp (-t)*(-1)); ring)
  apply (hd.div (hd.const_add 1) (ne_of_gt (by positivity : 0<1+z*Real.exp (-t)))).congr_deriv
  simp only [logisticTilt]
  field_simp
  ring

theorem hasDerivAt_logisticLogLaplace {z : ℝ} (hz : 0<z) (t : ℝ) :
    HasDerivAt (logisticLogLaplace z) (-logisticTilt z t) t := by
  have he : HasDerivAt (fun s : ℝ=>z*Real.exp (-s)) (-z*Real.exp (-t)) t := by
    convert (((hasDerivAt_id t).neg.exp).const_mul z) using 1
    all_goals first | rfl | (change -z*Real.exp (-t)=z*(Real.exp (-t)*(-1)); ring)
  have hd := ((he.const_add 1).log
    (ne_of_gt (by positivity : 0<1+z*Real.exp (-t)))).sub_const (Real.log (1+z))
  apply hd.congr_deriv
  simp only [logisticTilt, neg_mul, neg_div]

theorem logisticTilt_antitone {z : ℝ} (hz : 0<z) : Antitone (logisticTilt z) := by
  apply antitone_of_deriv_nonpos (fun t=>(hasDerivAt_logisticTilt hz t).differentiableAt)
  intro t
  rw [(hasDerivAt_logisticTilt hz t).deriv]
  exact neg_nonpos.mpr (mul_nonneg (logisticTilt_pos hz t).le (sub_nonneg.mpr (logisticTilt_lt_one hz t).le))

theorem logisticLogLaplace_eq {z : ℝ} (hz : 0<z) (t : ℝ) :
    logisticLogLaplace z t=Real.log (1-z/(1+z)+z/(1+z)*Real.exp (-t)) := by
  rw [logisticLogLaplace, ←Real.log_div (ne_of_gt (by positivity : 0<1+z*Real.exp (-t)))
    (ne_of_gt (by positivity : 0<1+z))]
  congr 1
  field_simp
  ring

theorem logisticLogLaplace_quadratic_lower {z u v : ℝ} (hz : 0<z) (hu : 0≤u)
    (hvar : ∀t∈Icc 0 u, v≤logisticTilt z t*(1-logisticTilt z t)) :
    -(z/(1+z))*u+v*u^2/2≤logisticLogLaplace z u := by
  have hd (t : ℝ) : HasDerivAt (fun t=>-logisticLogLaplace z t) (logisticTilt z t) t := by
    convert (hasDerivAt_logisticLogLaplace hz t).neg using 1 <;> first | rfl | simp
  have h := GaussianFiniteStep.finite_step_lower (G:=v) (c:=0) hu
    (fun t _=>hd t) (fun t _=>hasDerivAt_logisticTilt hz t)
    (fun t ht=>by simpa only [zero_mul,zero_div,sub_zero,neg_neg] using hvar t ht)
  simp only [logisticLogLaplace, logisticTilt, neg_zero, Real.exp_zero, mul_one,
    sub_self, neg_zero, zero_mul, zero_div, sub_zero] at h
  dsimp only [logisticLogLaplace]
  linarith

theorem bernoulli_variance_ge_min {lo hi q : ℝ} (hqlo : lo≤q) (hqhi : q≤hi) :
    min (lo*(1-lo)) (hi*(1-hi))≤q*(1-q) := by
  by_cases he : lo=hi
  · have hq : q=lo := by linarith
    simp [he,hq]
  · have hp : 0<hi-lo := sub_pos.mpr (lt_of_le_of_ne (hqlo.trans hqhi) he)
    have hminlo := min_le_left (lo*(1-lo)) (hi*(1-hi))
    have hminhi := min_le_right (lo*(1-lo)) (hi*(1-hi))
    have h₁ := mul_le_mul_of_nonneg_right hminlo (sub_nonneg.mpr hqhi)
    have h₂ := mul_le_mul_of_nonneg_right hminhi (sub_nonneg.mpr hqlo)
    nlinarith [mul_nonneg (sub_nonneg.mpr hqlo) (sub_nonneg.mpr hqhi)]

theorem logisticLogLaplace_quadratic_of_endpoints {z u U lo hi v : ℝ}
    (hz : 0<z) (hu : 0≤u) (huU : u≤U)
    (hlo : lo≤logisticTilt z U) (hhi : z/(1+z)≤hi)
    (hvlo : v≤lo*(1-lo)) (hvhi : v≤hi*(1-hi)) :
    -(z/(1+z))*u+v*u^2/2≤Real.log (1-z/(1+z)+z/(1+z)*Real.exp (-u)) := by
  rw [←logisticLogLaplace_eq hz]
  apply logisticLogLaplace_quadratic_lower hz hu
  intro t ht
  have hqlo := hlo.trans (logisticTilt_antitone hz (ht.2.trans huU))
  have hqhi : logisticTilt z t≤hi := by
    have hh := logisticTilt_antitone hz ht.1
    simp only [logisticTilt, neg_zero,Real.exp_zero,mul_one] at hh
    exact hh.trans hhi
  exact (le_min hvlo hvhi).trans (bernoulli_variance_ge_min hqlo hqhi)

/-- Exponential endpoint data can certify the whole tilt path, since the
logistic occupation is monotone in the underlying positive odds. -/
theorem logisticTilt_endpoint_lower {z U E : ℝ} (hz : 0<z) (_hE : 0<E)
    (hexp : Real.exp U≤E) : z/(E+z)≤logisticTilt z U := by
  have hid : logisticTilt z U=z/(Real.exp U+z) := by
    unfold logisticTilt
    rw [Real.exp_neg]
    field_simp
  rw [hid]
  exact div_le_div_of_nonneg_left hz.le (by positivity) (by linarith)

#print axioms logisticLogLaplace_quadratic_of_endpoints
#print axioms logisticTilt_endpoint_lower
end ForestUnimodality
