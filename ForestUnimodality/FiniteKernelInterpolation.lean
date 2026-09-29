import ForestUnimodality.BinomialDirectionParameter
import ForestUnimodality.BinomialParameterGaussian
import ForestUnimodality.AnalyticInterval

/-! Continuous parameter semantics for the finite mixture certificates.
Every residual is rebuilt from the actual binomial kernels and transform
charges. Endpoint positivity alone is not sufficient: the second-derivative
price below is paid on the entire closed interval. -/
namespace ForestUnimodality.FiniteKernelInterpolation

open Finset BinomialParameterDerivative

noncomputable def transform (n : ℕ) (t q : ℝ) : ℝ := (1 - q + q * t) ^ n

noncomputable def transformDerivative (n : ℕ) (t q : ℝ) : ℝ :=
  (n : ℝ) * (t - 1) * (1 - q + q * t) ^ (n - 1)

noncomputable def transformSecond (n : ℕ) (t q : ℝ) : ℝ :=
  (n : ℝ) * (n - 1 : ℕ) * (1 - t) ^ 2 * (1 - q + q * t) ^ (n - 2)

theorem hasDerivAt_transform (n : ℕ) (t q : ℝ) :
    HasDerivAt (transform n t) (transformDerivative n t q) q := by
  have h := (((hasDerivAt_const q 1).sub (hasDerivAt_id q)).add
    ((hasDerivAt_id q).mul_const t)).pow n
  convert h using 1 <;> first
    | rfl
    | (dsimp [transformDerivative]; ring)

theorem hasDerivAt_transformDerivative (n : ℕ) (t q : ℝ) :
    HasDerivAt (transformDerivative n t) (transformSecond n t q) q := by
  have h := (hasDerivAt_transform (n - 1) t q).const_mul ((n : ℝ) * (t - 1))
  change HasDerivAt (transformDerivative n t) _ q at h
  convert h using 1
  simp only [transformSecond, transformDerivative, Nat.sub_sub]
  norm_num only [Nat.reduceAdd]
  ring

theorem transformSecond_nonneg (n : ℕ) (t q : ℝ)
    (ht : 0 ≤ t) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ transformSecond n t q := by
  unfold transformSecond
  have hb : 0 ≤ 1 - q + q * t := add_nonneg (sub_nonneg.mpr hq.2) (mul_nonneg hq.1 ht)
  positivity

theorem transformSecond_le_lower (n : ℕ) {t a q : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (haq : a ≤ q)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    transformSecond n t q ≤ transformSecond n t a := by
  have hb : 0 ≤ 1 - q + q * t := add_nonneg (sub_nonneg.mpr hq.2) (mul_nonneg hq.1 ht0)
  have hab : 1 - q + q * t ≤ 1 - a + a * t := by
    nlinarith [mul_nonneg (sub_nonneg.mpr haq) (sub_nonneg.mpr ht1)]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb hab _)
    (by positivity : 0 ≤ (n : ℝ) * (n - 1 : ℕ) * (1 - t) ^ 2)

noncomputable def mixedDerivative (n : ℕ) (j : ℤ) (wL wR wC q : ℝ) : ℝ :=
  wL * leftDerivative n j q + wR * rightDerivative n j q + wC * centralDerivative n j q

noncomputable def mixedSecond (n : ℕ) (j : ℤ) (wL wR wC q : ℝ) : ℝ :=
  wL * leftSecond n j q + wR * rightSecond n j q + wC * centralSecond n j q

theorem hasDerivAt_mixed (n : ℕ) (j : ℤ) (wL wR wC q : ℝ) :
    HasDerivAt (fun x => binomialKernel n j x wL wR wC)
      (mixedDerivative n j wL wR wC q) q := by
  have h := (((hasDerivAt_left n j q).const_mul wL).add
    ((hasDerivAt_right n j q).const_mul wR)).add
    ((hasDerivAt_central n j q).const_mul wC)
  convert h using 1 <;> first
    | rfl
    | (ext x; simp [binomialKernel])

theorem hasDerivAt_mixedDerivative (n : ℕ) (j : ℤ) (wL wR wC q : ℝ) :
    HasDerivAt (mixedDerivative n j wL wR wC)
      (mixedSecond n j wL wR wC q) q := by
  exact (((hasDerivAt_leftDerivative n j q).const_mul wL).add
    ((hasDerivAt_rightDerivative n j q).const_mul wR)).add
    ((hasDerivAt_centralDerivative n j q).const_mul wC)

theorem mixedSecond_le {n : ℕ} {j : ℤ} {wL wR wC q BL BR BC : ℝ}
    (hwL : 0 ≤ wL) (hwR : 0 ≤ wR) (hwC : 0 ≤ wC)
    (hL : |leftSecond n j q| ≤ BL) (hR : |rightSecond n j q| ≤ BR)
    (hC : |centralSecond n j q| ≤ BC) :
    mixedSecond n j wL wR wC q ≤ wL * BL + wR * BR + wC * BC := by
  exact add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans hL) hwL)
    (mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans hR) hwR))
    (mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans hC) hwC)

structure Row (ι : Type*) where
  terms : Finset ι
  scale : ℝ
  A : ℝ
  B : ℝ
  C : ℝ
  dδ : ℝ
  dM : ℝ
  wL : ℝ
  wR : ℝ
  wC : ℝ
  price : ι → ℝ
  retention : ι → ℝ
  fixedPrice : ℤ → ℝ

noncomputable def Row.quadratic {ι : Type*} (r : Row ι) (n : ℕ) (j : ℤ) (q : ℝ) : ℝ :=
  -r.A - r.B * n - r.C * ((j : ℝ) - q * n) +
    r.dδ * ((j : ℝ) - q * n) ^ 2 + r.dM * (n : ℝ) ^ 2

noncomputable def Row.quadraticDerivative {ι : Type*} (r : Row ι)
    (n : ℕ) (j : ℤ) (q : ℝ) : ℝ :=
  r.C * n - 2 * r.dδ * n * ((j : ℝ) - q * n)

theorem Row.hasDerivAt_quadratic {ι : Type*} (r : Row ι) (n : ℕ) (j : ℤ) (q : ℝ) :
    HasDerivAt (r.quadratic n j) (r.quadraticDerivative n j q) q := by
  have hd := (hasDerivAt_const q (j : ℝ)).sub ((hasDerivAt_id q).mul_const (n : ℝ))
  have h := (((hasDerivAt_const q (-r.A - r.B * n)).sub (hd.const_mul r.C)).add
    ((hd.pow 2).const_mul r.dδ)).add_const (r.dM * (n : ℝ) ^ 2)
  convert h using 1 <;> first
    | rfl
    | (dsimp [quadraticDerivative]; ring)

theorem Row.hasDerivAt_quadraticDerivative {ι : Type*} (r : Row ι)
    (n : ℕ) (j : ℤ) (q : ℝ) :
    HasDerivAt (r.quadraticDerivative n j) (2 * r.dδ * (n : ℝ) ^ 2) q := by
  have hd := (hasDerivAt_const q (j : ℝ)).sub ((hasDerivAt_id q).mul_const (n : ℝ))
  have h := (hasDerivAt_const q (r.C * n)).sub (hd.const_mul (2 * r.dδ * n))
  convert h using 1 <;> first
    | rfl
    | ring

noncomputable def Row.residual {ι : Type*} (r : Row ι) (n : ℕ) (j : ℤ) (q : ℝ) : ℝ :=
  r.scale * binomialKernel n j q r.wL r.wR r.wC + r.quadratic n j q +
    (∑ i ∈ r.terms, r.price i * transform n (r.retention i) q) +
    r.fixedPrice j * transform n 0 q

noncomputable def Row.residualDerivative {ι : Type*} (r : Row ι)
    (n : ℕ) (j : ℤ) (q : ℝ) : ℝ :=
  r.scale * mixedDerivative n j r.wL r.wR r.wC q + r.quadraticDerivative n j q +
    (∑ i ∈ r.terms, r.price i * transformDerivative n (r.retention i) q) +
    r.fixedPrice j * transformDerivative n 0 q

noncomputable def Row.residualSecond {ι : Type*} (r : Row ι)
    (n : ℕ) (j : ℤ) (q : ℝ) : ℝ :=
  r.scale * mixedSecond n j r.wL r.wR r.wC q + 2 * r.dδ * (n : ℝ) ^ 2 +
    (∑ i ∈ r.terms, r.price i * transformSecond n (r.retention i) q) +
    r.fixedPrice j * transformSecond n 0 q

theorem Row.hasDerivAt_residual {ι : Type*} (r : Row ι) (n : ℕ) (j : ℤ) (q : ℝ) :
    HasDerivAt (r.residual n j) (r.residualDerivative n j q) q := by
  have hs := HasDerivAt.sum (u := r.terms) (fun i _ =>
    (hasDerivAt_transform n (r.retention i) q).const_mul (r.price i))
  have h := ((((hasDerivAt_mixed n j r.wL r.wR r.wC q).const_mul r.scale).add
    (r.hasDerivAt_quadratic n j q)).add hs).add
    ((hasDerivAt_transform n 0 q).const_mul (r.fixedPrice j))
  convert h using 1 <;> first
    | rfl
    | (ext x; simp [residual, Finset.sum_apply])

theorem Row.hasDerivAt_residualDerivative {ι : Type*} (r : Row ι)
    (n : ℕ) (j : ℤ) (q : ℝ) :
    HasDerivAt (r.residualDerivative n j) (r.residualSecond n j q) q := by
  have hs := HasDerivAt.sum (u := r.terms) (fun i _ =>
    (hasDerivAt_transformDerivative n (r.retention i) q).const_mul (r.price i))
  have h := ((((hasDerivAt_mixedDerivative n j r.wL r.wR r.wC q).const_mul r.scale).add
    (r.hasDerivAt_quadraticDerivative n j q)).add hs).add
    ((hasDerivAt_transformDerivative n 0 q).const_mul (r.fixedPrice j))
  convert h using 1 <;> first
    | rfl
    | (ext x; simp [residualDerivative, Finset.sum_apply])

noncomputable def Row.curvaturePrice {ι : Type*} (r : Row ι)
    (n : ℕ) (j : ℤ) (a BL BR BC : ℝ) : ℝ :=
  r.scale * (r.wL * BL + r.wR * BR + r.wC * BC) + 2 * r.dδ * (n : ℝ) ^ 2 +
    (∑ i ∈ r.terms, r.price i * transformSecond n (r.retention i) a) +
    r.fixedPrice j * transformSecond n 0 a

structure Row.Nonnegative {ι : Type*} (r : Row ι) : Prop where
  scale : 0 ≤ r.scale
  left : 0 ≤ r.wL
  right : 0 ≤ r.wR
  center : 0 ≤ r.wC
  delta : 0 ≤ r.dδ
  price : ∀ i ∈ r.terms, 0 ≤ r.price i
  retention : ∀ i ∈ r.terms, r.retention i ∈ Set.Icc (0 : ℝ) 1
  fixed : ∀ j, 0 ≤ r.fixedPrice j

theorem Row.residualSecond_le {ι : Type*} (r : Row ι) (hr : r.Nonnegative)
    (n : ℕ) (j : ℤ) {a q BL BR BC : ℝ} (haq : a ≤ q)
    (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hL : |leftSecond n j q| ≤ BL) (hR : |rightSecond n j q| ≤ BR)
    (hC : |centralSecond n j q| ≤ BC) :
    r.residualSecond n j q ≤ r.curvaturePrice n j a BL BR BC := by
  apply add_le_add
  · apply add_le_add
    · exact add_le_add (mul_le_mul_of_nonneg_left
        (mixedSecond_le hr.left hr.right hr.center hL hR hC) hr.scale) le_rfl
    · exact sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
        (transformSecond_le_lower n (hr.retention i hi).1 (hr.retention i hi).2 haq hq)
        (hr.price i hi)
  · exact mul_le_mul_of_nonneg_left
      (transformSecond_le_lower n (by norm_num) (by norm_num) haq hq) (hr.fixed j)

theorem Row.curvaturePrice_nonneg {ι : Type*} (r : Row ι) (hr : r.Nonnegative)
    (n : ℕ) (j : ℤ) {a BL BR BC : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hBL : 0 ≤ BL) (hBR : 0 ≤ BR) (hBC : 0 ≤ BC) :
    0 ≤ r.curvaturePrice n j a BL BR BC := by
  unfold curvaturePrice
  apply add_nonneg
  · apply add_nonneg
    · exact add_nonneg (mul_nonneg hr.scale (add_nonneg
        (add_nonneg (mul_nonneg hr.left hBL) (mul_nonneg hr.right hBR))
        (mul_nonneg hr.center hBC)))
        (mul_nonneg (mul_nonneg (by norm_num) hr.delta) (sq_nonneg _))
    · exact sum_nonneg fun i hi => mul_nonneg (hr.price i hi)
        (transformSecond_nonneg n (r.retention i) a (hr.retention i hi).1 ha)
  · exact mul_nonneg (hr.fixed j) (transformSecond_nonneg n 0 a (by norm_num) ha)

/-- Exact endpoint residual checks plus genuine uniform kernel curvature
bounds certify every real parameter, not just sampled values. -/
theorem Row.nonnegative_of_endpoints {ι : Type*} (r : Row ι) (hr : r.Nonnegative)
    (n : ℕ) (j : ℤ) {a b q BL BR BC : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b)
    (hBL : 0 ≤ BL) (hBR : 0 ≤ BR) (hBC : 0 ≤ BC)
    (hL : ∀ x ∈ Set.Icc a b, |leftSecond n j x| ≤ BL)
    (hR : ∀ x ∈ Set.Icc a b, |rightSecond n j x| ≤ BR)
    (hC : ∀ x ∈ Set.Icc a b, |centralSecond n j x| ≤ BC)
    (hleft : (b - a) ^ 2 * r.curvaturePrice n j a BL BR BC / 8 ≤ r.residual n j a)
    (hright : (b - a) ^ 2 * r.curvaturePrice n j a BL BR BC / 8 ≤ r.residual n j b)
    (hq : q ∈ Set.Icc a b) : 0 ≤ r.residual n j q := by
  apply AnalyticInterval.nonnegative_of_endpoint_curvature hab
    (r.curvaturePrice_nonneg hr n j ⟨ha, hab.trans hb⟩ hBL hBR hBC)
    ((continuous_iff_continuousAt.mpr fun x => (r.hasDerivAt_residual n j x).continuousAt).continuousOn)
    (fun x _ => r.hasDerivAt_residual n j x)
    (fun x _ => r.hasDerivAt_residualDerivative n j x) ?_ hleft hright hq
  intro x hx
  have hx' : x ∈ Set.Icc a b := ⟨hx.1.le, hx.2.le⟩
  exact r.residualSecond_le hr n j hx.1.le
    ⟨ha.trans hx.1.le, hx.2.le.trans hb⟩ (hL x hx') (hR x hx') (hC x hx')

/-- The endpoint theorem can be used immediately with the elementary sharp
coefficient bounds. Smaller proved Gaussian bounds may be supplied instead. -/
theorem Row.nonnegative_of_coarse_endpoints {ι : Type*} (r : Row ι) (hr : r.Nonnegative)
    (n : ℕ) (j : ℤ) {a b q : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b)
    (hleft : (b - a) ^ 2 * r.curvaturePrice n j a
      (2 * ((n + 1 : ℕ) : ℝ) * n) (2 * ((n + 1 : ℕ) : ℝ) * n)
      (6 * (n : ℝ) * (n - 1 : ℕ)) / 8 ≤ r.residual n j a)
    (hright : (b - a) ^ 2 * r.curvaturePrice n j a
      (2 * ((n + 1 : ℕ) : ℝ) * n) (2 * ((n + 1 : ℕ) : ℝ) * n)
      (6 * (n : ℝ) * (n - 1 : ℕ)) / 8 ≤ r.residual n j b)
    (hq : q ∈ Set.Icc a b) : 0 ≤ r.residual n j q := by
  apply r.nonnegative_of_endpoints hr n j ha hb hab
    (by positivity) (by positivity) (by positivity) ?_ ?_ ?_ hleft hright hq
  · intro x hx
    exact abs_leftSecond_le n j (ha.trans hx.1) (hx.2.trans hb)
  · intro x hx
    exact abs_rightSecond_le n j (ha.trans hx.1) (hx.2.trans hb)
  · intro x hx
    exact abs_centralSecond_le n j (ha.trans hx.1) (hx.2.trans hb)

/-- Both coarse and Gaussian estimates are now proved internally, including
all low-degree cases. The only analytic data here are finite scalar regime
checks and the two actual endpoint residual inequalities. -/
theorem Row.nonnegative_of_gaussian_endpoints {ι : Type*} (r : Row ι) (hr : r.Nonnegative)
    (n : ℕ) (j : ℤ) {a b q vmin c : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b)
    (hva : vmin ≤ a * (1 - a)) (hvb : vmin ≤ b * (1 - b))
    (hc : 0 < c) (hregime : (9 / 40 ≤ vmin ∧ c ≤ vmin) ∨
      (0 ≤ vmin ∧ c ≤ 4 * vmin / Real.pi ^ 2))
    (hleft : (b - a) ^ 2 * r.curvaturePrice n j a
      (BinomialParameterGaussian.directionBound n c) (BinomialParameterGaussian.directionBound n c)
      (BinomialParameterGaussian.centralBound n c) / 8 ≤ r.residual n j a)
    (hright : (b - a) ^ 2 * r.curvaturePrice n j a
      (BinomialParameterGaussian.directionBound n c) (BinomialParameterGaussian.directionBound n c)
      (BinomialParameterGaussian.centralBound n c) / 8 ≤ r.residual n j b)
    (hq : q ∈ Set.Icc a b) : 0 ≤ r.residual n j q := by
  have hd (x : ℝ) (hx : x ∈ Set.Icc a b) :
      BinomialParameterGaussian.DampingValid x c :=
    BinomialParameterGaussian.damping_of_interval hx.1 hx.2 hva hvb hc hregime
  have hda := hd a ⟨le_rfl, hab⟩
  have hBL : 0 ≤ BinomialParameterGaussian.directionBound n c :=
    (abs_nonneg _).trans (BinomialParameterGaussian.abs_leftSecond_bound n j hda)
  have hBC : 0 ≤ BinomialParameterGaussian.centralBound n c :=
    (abs_nonneg _).trans (BinomialParameterGaussian.abs_centralSecond_bound n j hda)
  exact r.nonnegative_of_endpoints hr n j ha hb hab hBL hBL hBC
    (fun x hx => BinomialParameterGaussian.abs_leftSecond_bound n j (hd x hx))
    (fun x hx => BinomialParameterGaussian.abs_rightSecond_bound n j (hd x hx))
    (fun x hx => BinomialParameterGaussian.abs_centralSecond_bound n j (hd x hx)) hleft hright hq

theorem Row.pointwise_lower_of_residual_nonneg {ι : Type*} (r : Row ι)
    (n : ℕ) (j : ℤ) (q : ℝ) (h : 0 ≤ r.residual n j q) :
    r.A + r.B * n + r.C * ((j : ℝ) - q * n) -
      r.dδ * ((j : ℝ) - q * n) ^ 2 - r.dM * (n : ℝ) ^ 2 -
      (∑ i ∈ r.terms, r.price i * (1 - q + q * r.retention i) ^ n) -
      r.fixedPrice j * (1 - q) ^ n ≤ r.scale * binomialKernel n j q r.wL r.wR r.wC := by
  simp only [residual, quadratic, transform, mul_zero, add_zero] at h
  linarith

#print axioms hasDerivAt_transform
#print axioms hasDerivAt_transformDerivative
#print axioms transformSecond_le_lower
#print axioms hasDerivAt_mixed
#print axioms hasDerivAt_mixedDerivative
#print axioms Row.hasDerivAt_residual
#print axioms Row.hasDerivAt_residualDerivative
#print axioms Row.residualSecond_le
#print axioms Row.nonnegative_of_endpoints
#print axioms Row.nonnegative_of_coarse_endpoints
#print axioms Row.nonnegative_of_gaussian_endpoints
#print axioms Row.pointwise_lower_of_residual_nonneg

end ForestUnimodality.FiniteKernelInterpolation
