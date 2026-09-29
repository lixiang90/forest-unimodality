import ForestUnimodality.CurvatureErrorLayerBudget
import ForestUnimodality.BinomialDirectionParameter

/-! Gaussian bounds for actual second derivatives in the Bernoulli
parameter. Their Fourier finite differences include all integer indices. -/
namespace ForestUnimodality.BinomialParameterGaussian
open Real Set MeasureTheory
open BinomialParameterDerivative

/-- Two proved full-period damping regimes, expressed only as numeric
conditions on the actual Bernoulli parameter. -/
def DampingValid (q c : ℝ) : Prop :=
  0<c ∧ ((9/40≤q*(1-q) ∧ c≤q*(1-q)) ∨
    (0≤q*(1-q) ∧ c≤4*(q*(1-q))/Real.pi^2))

theorem DampingValid.near {q c vmin : ℝ} (hc : 0<c) (hvmin : 9/40≤vmin)
    (hcv : c≤vmin) (hv : vmin≤q*(1-q)) : DampingValid q c :=
  ⟨hc,Or.inl ⟨hvmin.trans hv,hcv.trans hv⟩⟩

theorem DampingValid.period {q c vmin : ℝ} (hc : 0<c) (hvmin : 0≤vmin)
    (hcv : c≤4*vmin/Real.pi^2) (hv : vmin≤q*(1-q)) : DampingValid q c := by
  refine ⟨hc,Or.inr ⟨hvmin.trans hv,hcv.trans ?_⟩⟩
  gcongr

theorem characteristic_bound (M : ℕ) {q c t : ℝ} (h : DampingValid q c)
    (ht : |t|≤Real.pi) :
    ‖binomialCharacteristic M q t‖≤Real.exp (-((M:ℝ)*c)*t^2/2) := by
  rcases h.2 with hnear|hperiod
  · have he:=centeredBernoulliCharacteristic_pow_norm_le_gaussian M hnear.1 ht
    have he' : ‖binomialCharacteristic M q t‖≤Real.exp (-(M:ℝ)*(q*(1-q))*t^2/2) := by
      simpa only [norm_pow,centeredBernoulliCharacteristic_norm,binomialCharacteristic] using he
    apply he'.trans
    apply Real.exp_le_exp.mpr
    have hh:=mul_le_mul_of_nonneg_left hnear.2 (Nat.cast_nonneg M)
    nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg t)]
  · apply (binomialCharacteristic_norm_le_periodGaussian M hperiod.1 ht).trans
    apply Real.exp_le_exp.mpr
    have hh:=mul_le_mul_of_nonneg_left hperiod.2 (show 0≤(M:ℝ)*t^2/2 by positivity)
    calc
      -2*(M:ℝ)*(q*(1-q))*t^2/Real.pi^2 =
          -((M:ℝ)*t^2/2*(4*(q*(1-q))/Real.pi^2)) := by ring
      _ ≤ -((M:ℝ)*t^2/2*c) := neg_le_neg hh
      _ = _ := by ring

noncomputable def lattice (t : ℝ) : ℂ := ((2-2*Real.cos t:ℝ):ℂ)

theorem norm_lattice_le (t : ℝ) : ‖lattice t‖≤t^2 := by
  have h0 : 0≤2-2*Real.cos t := by linarith [Real.cos_le_one t]
  rw [lattice,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg h0,
    ←TriangularGaussian.lattice_identity]
  nlinarith [TriangularGaussian.kernel_le_one t,sq_nonneg t]

theorem periodFourier_lattice (f : ℝ→ℂ) (hf : Continuous f) (j : ℤ) :
    periodFourier (fun t=>lattice t*f t) j=
      2*periodFourier f j-periodFourier f (j-1)-periodFourier f (j+1) := by
  have he : (fun t=>lattice t*f t)=
      (fun t:ℝ=>2*f t-Complex.exp ((1:ℤ)*(t:ℂ)*Complex.I)*f t-
        Complex.exp ((-1:ℤ)*(t:ℂ)*Complex.I)*f t) := by
    funext t
    simp only [lattice,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_ofNat]
    rw [latticeMultiplier_eq_exp]
    have hm : ((-1:ℤ):ℂ)*(t:ℂ)*Complex.I=-((t:ℂ)*Complex.I) := by push_cast; ring
    rw [hm]
    simp only [Int.cast_one,one_mul]
    ring
  rw [he,periodFourier_sub _ _ (by fun_prop) (by fun_prop),
    periodFourier_sub _ _ (by fun_prop) (by fun_prop),periodFourier_const_mul,
    periodFourier_shift,periodFourier_shift]
  simp

theorem norm_periodFourier_le_even {a : ℝ} (ha : 0<a) (r : ℕ)
    {f : ℝ→ℂ} (hf : Continuous f)
    (hbound : ∀t∈Icc (-Real.pi) Real.pi,
      ‖f t‖≤t^(2*r)*Real.exp (-a*t^2/2)) (j : ℤ) :
    ‖periodFourier f j‖≤(2*Real.pi)⁻¹*∫t:ℝ,t^(2*r)*Real.exp (-a*t^2/2) := by
  have hh:=CurvatureErrorLayerBudget.norm_periodIntegral_le_even ha (by norm_num : (0:ℝ)≤1) r
    (f:=fun t=>Complex.exp (-((j:ℂ)*t*Complex.I))*f t) (by fun_prop) ?_
  · simpa only [one_mul,periodFourier,BinomialCurvatureError.periodIntegral] using hh
  · intro t ht
    have hp : ‖Complex.exp (-((j:ℂ)*(t:ℂ)*Complex.I))‖=1 := by rw [Complex.norm_exp]; simp
    rw [norm_mul,hp,one_mul,one_mul]
    exact hbound t ht

theorem second_difference_bound (M : ℕ) (hM : 0<M) (j : ℤ) {q c : ℝ}
    (h : DampingValid q c) :
    |2*binomialMass M j q-binomialMass M (j-1) q-binomialMass M (j+1) q|≤
      1/(Real.sqrt (2*Real.pi)*((M:ℝ)*c)*Real.sqrt ((M:ℝ)*c)) := by
  have hMr : 0<(M:ℝ) := by exact_mod_cast hM
  have ha : 0<(M:ℝ)*c := mul_pos hMr h.1
  have hh:=norm_periodFourier_le_even ha 1 (f:=fun t=>lattice t*binomialCharacteristic M q t)
    (by unfold lattice binomialCharacteristic; fun_prop) ?_ j
  · rw [show 2*1=2 by decide,GaussianKernelMoments.integral_second_fourier ha] at hh
    have he : periodFourier (fun t=>lattice t*binomialCharacteristic M q t) j=
      ((2*binomialMass M j q-binomialMass M (j-1) q-binomialMass M (j+1) q:ℝ):ℂ) := by
      simpa only [lattice,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_ofNat] using
        (binomial_curvature_eq_periodFourier M j q).symm
    rwa [he,Complex.norm_real,Real.norm_eq_abs] at hh
  · intro t ht
    rw [norm_mul]
    exact mul_le_mul (norm_lattice_le t) (characteristic_bound M h (abs_le.mpr ht))
      (norm_nonneg _) (sq_nonneg t)

theorem fourth_difference_fourier (M : ℕ) (j : ℤ) (q : ℝ) :
    ((binomialMass M (j-2) q-4*binomialMass M (j-1) q+6*binomialMass M j q-
      4*binomialMass M (j+1) q+binomialMass M (j+2) q:ℝ):ℂ)=
    periodFourier (fun t=>lattice t^2*binomialCharacteristic M q t) j := by
  have he : (fun t=>lattice t^2*binomialCharacteristic M q t)=
      (fun t=>lattice t*(lattice t*binomialCharacteristic M q t)) := by funext t; ring
  rw [he,periodFourier_lattice _ (by unfold lattice binomialCharacteristic; fun_prop)]
  rw [periodFourier_lattice _ (continuous_binomialCharacteristic M q),
    periodFourier_lattice _ (continuous_binomialCharacteristic M q),
    periodFourier_lattice _ (continuous_binomialCharacteristic M q)]
  simp only [←binomialMass_eq_periodFourier,
    show j-1-1=j-2 by omega,show j-1+1=j by omega,
    show j+1-1=j by omega,show j+1+1=j+2 by omega]
  push_cast
  ring

theorem fourth_difference_bound (M : ℕ) (hM : 0<M) (j : ℤ) {q c : ℝ}
    (h : DampingValid q c) :
    |binomialMass M (j-2) q-4*binomialMass M (j-1) q+6*binomialMass M j q-
      4*binomialMass M (j+1) q+binomialMass M (j+2) q|≤
      3/(Real.sqrt (2*Real.pi)*((M:ℝ)*c)^2*Real.sqrt ((M:ℝ)*c)) := by
  have hMr : 0<(M:ℝ) := by exact_mod_cast hM
  have ha : 0<(M:ℝ)*c := mul_pos hMr h.1
  have hh:=norm_periodFourier_le_even ha 2 (f:=fun t=>lattice t^2*binomialCharacteristic M q t)
    (by unfold lattice binomialCharacteristic; fun_prop) ?_ j
  · rw [show 2*2=4 by decide,GaussianKernelMoments.integral_fourth_fourier ha,
      ←fourth_difference_fourier,Complex.norm_real,Real.norm_eq_abs] at hh
    exact hh
  · intro t ht
    rw [norm_mul,norm_pow]
    have hl:=pow_le_pow_left₀ (norm_nonneg (lattice t)) (norm_lattice_le t) 2
    have he:=mul_le_mul hl (characteristic_bound M h (abs_le.mpr ht)) (norm_nonneg _)
      (sq_nonneg (t^2))
    simpa only [show 2*2=4 by decide,←pow_mul] using he

theorem abs_massSecond_gaussian (n : ℕ) (hn : 2<n) (j : ℤ) {q c : ℝ}
    (h : DampingValid q c) :
    |massSecond n j q|≤(n:ℝ)*(n-1:ℕ)/
      (Real.sqrt (2*Real.pi)*((n-2:ℕ)*c)*Real.sqrt ((n-2:ℕ)*c)) := by
  have hb:=second_difference_bound (n-2) (by omega) (j-1) h
  have he : |binomialMass (n-2) (j-2) q-2*binomialMass (n-2) (j-1) q+binomialMass (n-2) j q|≤
      1/(Real.sqrt (2*Real.pi)*((n-2:ℕ)*c)*Real.sqrt ((n-2:ℕ)*c)) := by
    rw [show j-1-1=j-2 by omega,show j-1+1=j by omega] at hb
    have heq : binomialMass (n-2) (j-2) q-2*binomialMass (n-2) (j-1) q+binomialMass (n-2) j q=
        -(2*binomialMass (n-2) (j-1) q-binomialMass (n-2) (j-2) q-binomialMass (n-2) j q) := by ring
    simpa only [heq,abs_neg] using hb
  unfold massSecond
  rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg n),abs_of_nonneg (Nat.cast_nonneg (n-1))]
  calc
    _ ≤ (n:ℝ)*(n-1:ℕ)*(1/(Real.sqrt (2*Real.pi)*((n-2:ℕ)*c)*Real.sqrt ((n-2:ℕ)*c))) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

theorem abs_centralSecond_gaussian (n : ℕ) (hn : 2<n) (j : ℤ) {q c : ℝ}
    (h : DampingValid q c) :
    |centralSecond n j q|≤3*(n:ℝ)*(n-1:ℕ)/
      (Real.sqrt (2*Real.pi)*((n-2:ℕ)*c)^2*Real.sqrt ((n-2:ℕ)*c)) := by
  have hb:=fourth_difference_bound (n-2) (by omega) (j-1) h
  rw [show j-1-2=j-3 by omega,show j-1-1=j-2 by omega,
    show j-1+1=j by omega,show j-1+2=j+1 by omega] at hb
  have heq : -binomialMass (n-2) (j-3) q+4*binomialMass (n-2) (j-2) q-
      6*binomialMass (n-2) (j-1) q+4*binomialMass (n-2) j q-binomialMass (n-2) (j+1) q=
      -(binomialMass (n-2) (j-3) q-4*binomialMass (n-2) (j-2) q+
      6*binomialMass (n-2) (j-1) q-4*binomialMass (n-2) j q+binomialMass (n-2) (j+1) q) := by ring
  unfold centralSecond
  rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg n),abs_of_nonneg (Nat.cast_nonneg (n-1)),heq,abs_neg]
  calc
    _ ≤ (n:ℝ)*(n-1:ℕ)*(3/(Real.sqrt (2*Real.pi)*((n-2:ℕ)*c)^2*Real.sqrt ((n-2:ℕ)*c))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- Degree elevation does not lose a support factor: outside the elevated
support the actual second derivative is identically zero. -/
theorem abs_leftSecond_gaussian (n : ℕ) (hn : 1<n) (j : ℤ) {q c : ℝ}
    (h : DampingValid q c) :
    |leftSecond n j q|≤((n+1:ℕ):ℝ)*n/
      (Real.sqrt (2*Real.pi)*((n-1:ℕ)*c)*Real.sqrt ((n-1:ℕ)*c)) := by
  unfold leftSecond
  by_cases hj : 0≤j ∧ j≤(n+1:ℕ)
  · rw [abs_mul]
    calc
      _ ≤ 1*|massSecond (n+1) j q| :=
        mul_le_mul_of_nonneg_right (abs_leftFactor_le_one n j hj.1 hj.2) (abs_nonneg _)
      _ ≤ _ := by
        simpa only [one_mul,Nat.add_sub_cancel,
          show n+1-2=n-1 by omega] using abs_massSecond_gaussian (n+1) (by omega) j h
  · rw [massSecond_eq_zero_of_outside (n+1) j hj q]
    simp only [mul_zero,abs_zero]
    have hc:=h.1
    positivity

theorem abs_rightSecond_gaussian (n : ℕ) (hn : 1<n) (j : ℤ) {q c : ℝ}
    (h : DampingValid q c) :
    |rightSecond n j q|≤((n+1:ℕ):ℝ)*n/
      (Real.sqrt (2*Real.pi)*((n-1:ℕ)*c)*Real.sqrt ((n-1:ℕ)*c)) := by
  simpa only [rightSecond,abs_neg] using abs_leftSecond_gaussian n hn (j+1) h

theorem inv_sqrt_two_pi_lt : 1/Real.sqrt (2*Real.pi)<(2/5:ℝ) := by
  have hp:=Real.pi_gt_d2
  have hs:=Real.sq_sqrt (show 0≤2*Real.pi by positivity)
  have hs0:=Real.sqrt_nonneg (2*Real.pi)
  have hspos : 0<Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  apply (div_lt_iff₀ hspos).mpr
  nlinarith

private theorem safe_gaussian_coefficient {C d : ℝ} (hC : 0≤C) (hd : 0<d) :
    C/(Real.sqrt (2*Real.pi)*d)≤2*C/(5*d) := by
  have hh:=mul_le_mul_of_nonneg_left inv_sqrt_two_pi_lt.le (div_nonneg hC hd.le)
  calc
    _ = (C/d)*(1/Real.sqrt (2*Real.pi)) := by ring
    _ ≤ (C/d)*(2/5) := hh
    _ = _ := by ring

theorem abs_massSecond_safe (n : ℕ) (hn : 2<n) (j : ℤ) {q c : ℝ}
    (h : DampingValid q c) :
    |massSecond n j q|≤2*(n:ℝ)*(n-1:ℕ)/
      (5*((n-2:ℕ)*c)*Real.sqrt ((n-2:ℕ)*c)) := by
  apply (abs_massSecond_gaussian n hn j h).trans
  have hn2 : 0<((n-2:ℕ):ℝ) := by exact_mod_cast (show 0<n-2 by omega)
  have hc:=h.1
  have hh:=safe_gaussian_coefficient (show 0≤(n:ℝ)*(n-1:ℕ) by positivity)
    (show 0<((n-2:ℕ)*c)*Real.sqrt ((n-2:ℕ)*c) by positivity)
  simpa only [mul_assoc] using hh

theorem abs_centralSecond_safe (n : ℕ) (hn : 2<n) (j : ℤ) {q c : ℝ}
    (h : DampingValid q c) :
    |centralSecond n j q|≤6*(n:ℝ)*(n-1:ℕ)/
      (5*((n-2:ℕ)*c)^2*Real.sqrt ((n-2:ℕ)*c)) := by
  apply (abs_centralSecond_gaussian n hn j h).trans
  have hn2 : 0<((n-2:ℕ):ℝ) := by exact_mod_cast (show 0<n-2 by omega)
  have hc:=h.1
  have hh:=safe_gaussian_coefficient (show 0≤3*(n:ℝ)*(n-1:ℕ) by positivity)
    (show 0<((n-2:ℕ)*c)^2*Real.sqrt ((n-2:ℕ)*c) by positivity)
  calc
    _ = (3*(n:ℝ)*(n-1:ℕ))/(Real.sqrt (2*Real.pi)*(((n-2:ℕ)*c)^2*Real.sqrt ((n-2:ℕ)*c))) := by ring
    _ ≤ 2*(3*(n:ℝ)*(n-1:ℕ))/(5*(((n-2:ℕ)*c)^2*Real.sqrt ((n-2:ℕ)*c))) := hh
    _ = _ := by ring

theorem abs_leftSecond_safe (n : ℕ) (hn : 1<n) (j : ℤ) {q c : ℝ}
    (h : DampingValid q c) :
    |leftSecond n j q|≤2*((n+1:ℕ):ℝ)*n/
      (5*((n-1:ℕ)*c)*Real.sqrt ((n-1:ℕ)*c)) := by
  apply (abs_leftSecond_gaussian n hn j h).trans
  have hn1 : 0<((n-1:ℕ):ℝ) := by exact_mod_cast (show 0<n-1 by omega)
  have hc:=h.1
  have hh:=safe_gaussian_coefficient (show 0≤((n+1:ℕ):ℝ)*n by positivity)
    (show 0<((n-1:ℕ)*c)*Real.sqrt ((n-1:ℕ)*c) by positivity)
  simpa only [mul_assoc] using hh

theorem abs_rightSecond_safe (n : ℕ) (hn : 1<n) (j : ℤ) {q c : ℝ}
    (h : DampingValid q c) :
    |rightSecond n j q|≤2*((n+1:ℕ):ℝ)*n/
      (5*((n-1:ℕ)*c)*Real.sqrt ((n-1:ℕ)*c)) := by
  simpa only [rightSecond,abs_neg] using abs_leftSecond_safe n hn (j+1) h

private theorem rpow_three_halves {x : ℝ} (hx : 0<x) :
    x^(3/2:ℝ)=x*Real.sqrt x := by
  rw [show (3/2:ℝ)=(1:ℕ)+(1/2:ℝ) by norm_num,Real.rpow_add hx,
    Real.rpow_natCast,pow_one,←Real.sqrt_eq_rpow]

private theorem rpow_five_halves {x : ℝ} (hx : 0<x) :
    x^(5/2:ℝ)=x^2*Real.sqrt x := by
  rw [show (5/2:ℝ)=(2:ℕ)+(1/2:ℝ) by norm_num,Real.rpow_add hx,
    Real.rpow_natCast,←Real.sqrt_eq_rpow]

/-- The original stage170 (6.1) power notation, with a kernel-proved safe
rational constant and all integer indices, including outside support. -/
theorem abs_centralSecond_safe_rpow (n : ℕ) (hn : 2<n) (j : ℤ) {q c : ℝ}
    (h : DampingValid q c) :
    |centralSecond n j q|≤6*(n:ℝ)*(n-1:ℕ)/(5*(((n-2:ℕ):ℝ)*c)^(5/2:ℝ)) := by
  have hn2 : 0<((n-2:ℕ):ℝ) := by exact_mod_cast (show 0<n-2 by omega)
  rw [rpow_five_halves (mul_pos hn2 h.1),←mul_assoc]
  exact abs_centralSecond_safe n hn j h

theorem abs_leftSecond_safe_rpow (n : ℕ) (hn : 1<n) (j : ℤ) {q c : ℝ}
    (h : DampingValid q c) :
    |leftSecond n j q|≤2*((n+1:ℕ):ℝ)*n/(5*(((n-1:ℕ):ℝ)*c)^(3/2:ℝ)) := by
  have hn1 : 0<((n-1:ℕ):ℝ) := by exact_mod_cast (show 0<n-1 by omega)
  rw [rpow_three_halves (mul_pos hn1 h.1),←mul_assoc]
  exact abs_leftSecond_safe n hn j h

theorem abs_rightSecond_safe_rpow (n : ℕ) (hn : 1<n) (j : ℤ) {q c : ℝ}
    (h : DampingValid q c) :
    |rightSecond n j q|≤2*((n+1:ℕ):ℝ)*n/(5*(((n-1:ℕ):ℝ)*c)^(3/2:ℝ)) := by
  simpa only [rightSecond,abs_neg] using abs_leftSecond_safe_rpow n hn (j+1) h

/-- Endpoint lower bounds control every interior Bernoulli variance by the
actual concavity of q(1-q), not by interval sampling. -/
theorem variance_lower_interval {qa qb q vmin : ℝ}
    (hqa : qa≤q) (hqb : q≤qb)
    (ha : vmin≤qa*(1-qa)) (hb : vmin≤qb*(1-qb)) : vmin≤q*(1-q) := by
  by_cases hq : q≤1/2
  · have hh:=mul_nonneg (sub_nonneg.mpr hqa) (show 0≤1-q-qa by linarith)
    nlinarith
  · have hh:=mul_nonneg (sub_nonneg.mpr hqb) (show 0≤qb+q-1 by linarith)
    nlinarith

theorem damping_of_interval {qa qb q vmin c : ℝ}
    (hqa : qa≤q) (hqb : q≤qb)
    (ha : vmin≤qa*(1-qa)) (hb : vmin≤qb*(1-qb))
    (hc : 0<c) (hregime : (9/40≤vmin ∧ c≤vmin) ∨
      (0≤vmin ∧ c≤4*vmin/Real.pi^2)) : DampingValid q c := by
  have hv:=variance_lower_interval hqa hqb ha hb
  rcases hregime with hh|hh
  · exact DampingValid.near hc hh.1 hh.2 hv
  · exact DampingValid.period hc hh.1 hh.2 hv

/-- A single finite numeric regime proves the derivative budget on the
entire closed parameter interval and all integer binomial indices. -/
theorem centralSecond_interval_bound (n : ℕ) (hn : 2<n)
    {qa qb vmin c : ℝ} (ha : vmin≤qa*(1-qa)) (hb : vmin≤qb*(1-qb))
    (hc : 0<c) (hregime : (9/40≤vmin ∧ c≤vmin) ∨
      (0≤vmin ∧ c≤4*vmin/Real.pi^2)) :
    ∀q∈Icc qa qb,∀j:ℤ,|centralSecond n j q|≤
      6*(n:ℝ)*(n-1:ℕ)/(5*(((n-2:ℕ):ℝ)*c)^(5/2:ℝ)) := by
  intro q hq j
  exact abs_centralSecond_safe_rpow n hn j (damping_of_interval hq.1 hq.2 ha hb hc hregime)

theorem leftSecond_interval_bound (n : ℕ) (hn : 1<n)
    {qa qb vmin c : ℝ} (ha : vmin≤qa*(1-qa)) (hb : vmin≤qb*(1-qb))
    (hc : 0<c) (hregime : (9/40≤vmin ∧ c≤vmin) ∨
      (0≤vmin ∧ c≤4*vmin/Real.pi^2)) :
    ∀q∈Icc qa qb,∀j:ℤ,|leftSecond n j q|≤
      2*((n+1:ℕ):ℝ)*n/(5*(((n-1:ℕ):ℝ)*c)^(3/2:ℝ)) := by
  intro q hq j
  exact abs_leftSecond_safe_rpow n hn j (damping_of_interval hq.1 hq.2 ha hb hc hregime)

theorem rightSecond_interval_bound (n : ℕ) (hn : 1<n)
    {qa qb vmin c : ℝ} (ha : vmin≤qa*(1-qa)) (hb : vmin≤qb*(1-qb))
    (hc : 0<c) (hregime : (9/40≤vmin ∧ c≤vmin) ∨
      (0≤vmin ∧ c≤4*vmin/Real.pi^2)) :
    ∀q∈Icc qa qb,∀j:ℤ,|rightSecond n j q|≤
      2*((n+1:ℕ):ℝ)*n/(5*(((n-1:ℕ):ℝ)*c)^(3/2:ℝ)) := by
  intro q hq j
  exact abs_rightSecond_safe_rpow n hn j (damping_of_interval hq.1 hq.2 ha hb hc hregime)

theorem DampingValid.q_mem {q c : ℝ} (h : DampingValid q c) : q∈Icc 0 1 := by
  have hv : 0≤q*(1-q) := by
    rcases h.2 with hh|hh
    · linarith [hh.1]
    · exact hh.1
  constructor <;> nlinarith

/-- Exact low-degree conventions: degrees 0 and 1 cost zero, degree 2
costs 12; larger degrees take the smaller of two proved bounds. -/
noncomputable def centralBound (n : ℕ) (c : ℝ) : ℝ :=
  if 2<n then min (6*(n:ℝ)*(n-1:ℕ))
    (6*(n:ℝ)*(n-1:ℕ)/(5*(((n-2:ℕ):ℝ)*c)^(5/2:ℝ)))
  else 6*(n:ℝ)*(n-1:ℕ)

/-- Directional degree is n+1: original n=0 costs zero and n=1 costs 4. -/
noncomputable def directionBound (n : ℕ) (c : ℝ) : ℝ :=
  if 1<n then min (2*((n+1:ℕ):ℝ)*n)
    (2*((n+1:ℕ):ℝ)*n/(5*(((n-1:ℕ):ℝ)*c)^(3/2:ℝ)))
  else 2*((n+1:ℕ):ℝ)*n

theorem abs_centralSecond_bound (n : ℕ) (j : ℤ) {q c : ℝ} (h : DampingValid q c) :
    |centralSecond n j q|≤centralBound n c := by
  have hq:=h.q_mem
  unfold centralBound
  split_ifs with hn
  · exact le_min (abs_centralSecond_le n j hq.1 hq.2) (abs_centralSecond_safe_rpow n hn j h)
  · exact abs_centralSecond_le n j hq.1 hq.2

theorem abs_leftSecond_bound (n : ℕ) (j : ℤ) {q c : ℝ} (h : DampingValid q c) :
    |leftSecond n j q|≤directionBound n c := by
  have hq:=h.q_mem
  unfold directionBound
  split_ifs with hn
  · exact le_min (abs_leftSecond_le n j hq.1 hq.2) (abs_leftSecond_safe_rpow n hn j h)
  · exact abs_leftSecond_le n j hq.1 hq.2

theorem abs_rightSecond_bound (n : ℕ) (j : ℤ) {q c : ℝ} (h : DampingValid q c) :
    |rightSecond n j q|≤directionBound n c := by
  simpa only [rightSecond,abs_neg] using abs_leftSecond_bound n (j+1) h

theorem centralBound_small (c : ℝ) : centralBound 0 c=0 ∧ centralBound 1 c=0 ∧ centralBound 2 c=12 := by
  norm_num [centralBound]

theorem directionBound_small (c : ℝ) : directionBound 0 c=0 ∧ directionBound 1 c=4 := by
  norm_num [directionBound]

/-- Direct second derivatives of the original central kernel, with no
analytic derivative premise left for downstream interval certificates. -/
theorem actual_central_deriv2_bound (n : ℕ) (j : ℤ) {q c : ℝ} (h : DampingValid q c) :
    |deriv (deriv (fun x=>binomialKernel n j x 0 0 1)) q|≤centralBound n c := by
  have he : deriv (fun x=>binomialKernel n j x 0 0 1)=centralDerivative n j := by
    funext x
    exact (hasDerivAt_central n j x).deriv
  rw [he,(hasDerivAt_centralDerivative n j q).deriv]
  exact abs_centralSecond_bound n j h

theorem actual_left_deriv2_bound (n : ℕ) (j : ℤ) {q c : ℝ} (h : DampingValid q c) :
    |deriv (deriv (fun x=>binomialKernel n j x 1 0 0)) q|≤directionBound n c := by
  have he : deriv (fun x=>binomialKernel n j x 1 0 0)=leftDerivative n j := by
    funext x
    exact (hasDerivAt_left n j x).deriv
  rw [he,(hasDerivAt_leftDerivative n j q).deriv]
  exact abs_leftSecond_bound n j h

theorem actual_right_deriv2_bound (n : ℕ) (j : ℤ) {q c : ℝ} (h : DampingValid q c) :
    |deriv (deriv (fun x=>binomialKernel n j x 0 1 0)) q|≤directionBound n c := by
  have he : deriv (fun x=>binomialKernel n j x 0 1 0)=rightDerivative n j := by
    funext x
    exact (hasDerivAt_right n j x).deriv
  rw [he,(hasDerivAt_rightDerivative n j q).deriv]
  exact abs_rightSecond_bound n j h

#print axioms actual_central_deriv2_bound
#print axioms actual_left_deriv2_bound
#print axioms actual_right_deriv2_bound
#print axioms centralSecond_interval_bound
#print axioms leftSecond_interval_bound
#print axioms rightSecond_interval_bound
#print axioms abs_leftSecond_safe_rpow
#print axioms abs_rightSecond_safe_rpow
#print axioms abs_centralSecond_safe_rpow
#print axioms abs_massSecond_gaussian
#print axioms abs_centralSecond_gaussian
end ForestUnimodality.BinomialParameterGaussian
