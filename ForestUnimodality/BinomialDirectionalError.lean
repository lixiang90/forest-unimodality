import ForestUnimodality.BinomialPointMassError
import ForestUnimodality.BernoulliGaussianError
import ForestUnimodality.BinomialCurvatureError

/-! A single Fourier error measure controls mass and a signed adjacent
coefficient together. The zeroth and second moments are not errors from two
unrelated estimates: they bound the same nonnegative integrand. -/
namespace ForestUnimodality.BinomialDirectionalError
open Real Set MeasureTheory BinomialPointMassError BinomialCurvatureError

noncomputable def multiplier (r t : ℝ) : ℂ :=
  1-(r:ℂ)*oscillation 1 t

theorem multiplier_norm_sq (r t : ℝ) :
    ‖multiplier r t‖^2=(1-r)^2+2*r*(1-Real.cos t) := by
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp [multiplier,BinomialCurvatureError.oscillation,Complex.exp_re,Complex.exp_im]
  have h:=Real.sin_sq_add_cos_sq t
  nlinarith [congrArg (fun x:ℝ=>r^2*x) h]

theorem multiplier_norm_sq_le {r : ℝ} (hr : 0≤r) (t : ℝ) :
    ‖multiplier r t‖^2≤(1-r)^2+r*t^2 := by
  rw [multiplier_norm_sq]
  nlinarith [mul_le_mul_of_nonneg_left
    (Real.one_sub_sq_div_two_le_cos (x:=t)) hr]

theorem multiplier_norm_young {r s : ℝ} (hr : 0≤r) (hs : 0<s) (t : ℝ) :
    ‖multiplier r t‖≤(s^2+(1-r)^2)/(2*s)+(r/(2*s))*t^2 := by
  have hsq:=sq_nonneg (‖multiplier r t‖-s)
  have hb:=multiplier_norm_sq_le hr t
  have he : (s^2+(1-r)^2)/(2*s)+(r/(2*s))*t^2=
      (s^2+(1-r)^2+r*t^2)/(2*s) := by ring_nf
  rw [he]
  apply (le_div_iff₀ (by positivity : 0<2*s)).mpr
  nlinarith

theorem young_optimize {A B Z : ℝ} (hA : 0<A) (hB : 0<B)
    (h : ∀s>0,Z≤(s^2*A+B)/(2*s)) : Z≤Real.sqrt (A*B) := by
  let R:=Real.sqrt (A*B)
  have hR : 0<R := Real.sqrt_pos.mpr (mul_pos hA hB)
  have hR2 : R^2=A*B := Real.sq_sqrt (mul_pos hA hB).le
  have he : (((R/A)^2*A+B)/(2*(R/A)))=R := by
    field_simp
    nlinarith
  exact (h (R/A) (div_pos hR hA)).trans_eq he

noncomputable def majorant (b c₃ c₄ t : ℝ) : ℝ :=
  c₃*(|t|^3*Real.exp (-b*t^2/2))+c₄*(t^4*Real.exp (-b*t^2/2))

theorem integrable_majorant {b : ℝ} (hb : 0<b) (c₃ c₄ : ℝ) :
    Integrable (majorant b c₃ c₄) := by
  have h3 : Integrable (fun t:ℝ=>|t|^3*Real.exp (-b*t^2/2)) := by
    simpa only [Real.norm_eq_abs,abs_mul,abs_pow,abs_of_pos (Real.exp_pos _)] using
      (GaussianCurvatureTail.integrable_real_moment hb 3).norm
  exact (h3.const_mul c₃).add ((GaussianCurvatureTail.integrable_real_moment hb 4).const_mul c₄)

theorem integrable_second_majorant {b : ℝ} (hb : 0<b) (c₃ c₄ : ℝ) :
    Integrable (fun t:ℝ=>t^2*majorant b c₃ c₄ t) := by
  have h5 : Integrable (fun t:ℝ=>|t|^5*Real.exp (-b*t^2/2)) := by
    simpa only [Real.norm_eq_abs,abs_mul,abs_pow,abs_of_pos (Real.exp_pos _)] using
      (GaussianCurvatureTail.integrable_real_moment hb 5).norm
  have he : (fun t:ℝ=>t^2*majorant b c₃ c₄ t)=
      (fun t=>c₃*(|t|^5*Real.exp (-b*t^2/2))+c₄*(t^6*Real.exp (-b*t^2/2))) := by
    funext t
    unfold majorant
    rw [show t^4=(t^2)^2 by ring_nf,show t^6=(t^2)^3 by ring_nf,←sq_abs t]
    ring_nf
  rw [he]
  exact (h5.const_mul c₃).add ((GaussianCurvatureTail.integrable_real_moment hb 6).const_mul c₄)

theorem integral_majorant {b : ℝ} (hb : 0<b) (c₃ c₄ : ℝ) :
    (2*Real.pi)⁻¹*(∫t:ℝ,majorant b c₃ c₄ t)=
      c₃*(2/(Real.pi*b^2))+c₄*(3/(Real.sqrt (2*Real.pi)*b^2*Real.sqrt b)) := by
  have h3 : Integrable (fun t:ℝ=>|t|^3*Real.exp (-b*t^2/2)) := by
    simpa only [Real.norm_eq_abs,abs_mul,abs_pow,abs_of_pos (Real.exp_pos _)] using
      (GaussianCurvatureTail.integrable_real_moment hb 3).norm
  unfold majorant
  rw [integral_add (h3.const_mul _) ((GaussianCurvatureTail.integrable_real_moment hb 4).const_mul _),
    integral_const_mul,integral_const_mul]
  calc
    _ = c₃*((2*Real.pi)⁻¹*∫t:ℝ,|t|^3*Real.exp (-b*t^2/2))+
      c₄*((2*Real.pi)⁻¹*∫t:ℝ,t^4*Real.exp (-b*t^2/2)) := by ring_nf
    _ = _ := by rw [GaussianKernelMoments.integral_absCubic_fourier hb,
      GaussianKernelMoments.integral_fourth_fourier hb]

theorem integral_second_majorant {b : ℝ} (hb : 0<b) (c₃ c₄ : ℝ) :
    (2*Real.pi)⁻¹*(∫t:ℝ,t^2*majorant b c₃ c₄ t)=
      c₃*(8/(Real.pi*b^3))+c₄*(15/(Real.sqrt (2*Real.pi)*b^3*Real.sqrt b)) := by
  have h5 : Integrable (fun t:ℝ=>|t|^5*Real.exp (-b*t^2/2)) := by
    simpa only [Real.norm_eq_abs,abs_mul,abs_pow,abs_of_pos (Real.exp_pos _)] using
      (GaussianCurvatureTail.integrable_real_moment hb 5).norm
  have he : (fun t:ℝ=>t^2*majorant b c₃ c₄ t)=
      (fun t=>c₃*(|t|^5*Real.exp (-b*t^2/2))+c₄*(t^6*Real.exp (-b*t^2/2))) := by
    funext t
    unfold majorant
    rw [show t^4=(t^2)^2 by ring_nf,show t^6=(t^2)^3 by ring_nf,←sq_abs t]
    ring_nf
  rw [he,integral_add (h5.const_mul _) ((GaussianCurvatureTail.integrable_real_moment hb 6).const_mul _),
    integral_const_mul,integral_const_mul]
  calc
    _ = c₃*((2*Real.pi)⁻¹*∫t:ℝ,|t|^5*Real.exp (-b*t^2/2))+
      c₄*((2*Real.pi)⁻¹*∫t:ℝ,t^6*Real.exp (-b*t^2/2)) := by ring_nf
    _ = _ := by rw [GaussianKernelMoments.integral_absFifth_fourier hb,
      GaussianKernelMoments.integral_sixth_fourier hb]

theorem norm_period_le_majorant {b c₃ c₄ c₀ c₂ : ℝ}
    (hb : 0<b) (hc₃ : 0≤c₃) (hc₄ : 0≤c₄) (hc₀ : 0≤c₀) (hc₂ : 0≤c₂)
    {f : ℝ→ℂ} (hf : Continuous f)
    (hbound : ∀t∈Icc (-Real.pi) Real.pi,
      ‖f t‖≤c₀*majorant b c₃ c₄ t+c₂*(t^2*majorant b c₃ c₄ t)) :
    ‖periodIntegral f‖≤
      c₀*(c₃*(2/(Real.pi*b^2))+c₄*(3/(Real.sqrt (2*Real.pi)*b^2*Real.sqrt b)))+
      c₂*(c₃*(8/(Real.pi*b^3))+c₄*(15/(Real.sqrt (2*Real.pi)*b^3*Real.sqrt b))) := by
  let g:=fun t:ℝ=>c₀*majorant b c₃ c₄ t+c₂*(t^2*majorant b c₃ c₄ t)
  have hg : Integrable g := ((integrable_majorant hb c₃ c₄).const_mul c₀).add
    ((integrable_second_majorant hb c₃ c₄).const_mul c₂)
  have hgc : Continuous g := by dsimp [g,majorant]; fun_prop
  have hg0 (t:ℝ) : 0≤g t := by dsimp [g,majorant]; positivity
  have horder : -Real.pi≤Real.pi := by linarith [Real.pi_pos]
  have hm : (∫t in -Real.pi..Real.pi,‖f t‖)≤∫t in -Real.pi..Real.pi,g t :=
    intervalIntegral.integral_mono_on horder (hf.norm.intervalIntegrable _ _)
      (hgc.intervalIntegrable _ _) hbound
  have hfull : (∫t in -Real.pi..Real.pi,g t)≤∫t:ℝ,g t := by
    rw [intervalIntegral.integral_of_le horder]
    exact setIntegral_le_integral hg (Filter.Eventually.of_forall hg0)
  have hn : ‖periodIntegral f‖≤(2*Real.pi)⁻¹*(∫t:ℝ,g t) := by
    rw [periodIntegral,norm_mul,norm_normalizer]
    exact mul_le_mul_of_nonneg_left
      ((intervalIntegral.norm_integral_le_integral_norm horder).trans (hm.trans hfull)) (by positivity)
  refine hn.trans_eq ?_
  dsimp only [g]
  rw [integral_add ((integrable_majorant hb c₃ c₄).const_mul c₀)
    ((integrable_second_majorant hb c₃ c₄).const_mul c₂),integral_const_mul,integral_const_mul]
  calc
    _ = c₀*((2*Real.pi)⁻¹*∫t:ℝ,majorant b c₃ c₄ t)+
      c₂*((2*Real.pi)⁻¹*∫t:ℝ,t^2*majorant b c₃ c₄ t) := by ring_nf
    _ = _ := by rw [integral_majorant hb,integral_second_majorant hb]

noncomputable def centralZero (m : ℕ) (q : ℝ) : ℝ :=
  let v:=q*(1-q)
  let b:=((m-1:ℕ):ℝ)*v
  (m:ℝ)*v*|1-2*q|/(3*Real.pi*b^2)+
    (m:ℝ)*v/(16*Real.sqrt (2*Real.pi)*b^2*Real.sqrt b)

noncomputable def centralTwo (m : ℕ) (q : ℝ) : ℝ :=
  let v:=q*(1-q)
  let b:=((m-1:ℕ):ℝ)*v
  4*(m:ℝ)*v*|1-2*q|/(3*Real.pi*b^3)+
    5*(m:ℝ)*v/(16*Real.sqrt (2*Real.pi)*b^3*Real.sqrt b)

noncomputable def centralIntegrand (m : ℕ) (q d r t : ℝ) : ℂ :=
  multiplier r t*oscillation d t*(centeredBernoulliCharacteristic q t^m-
    (Real.exp (-(m:ℝ)*(q*(1-q))*t^2/2):ℂ))

/-- Both moments come from the same actual centered characteristic error,
before any averaging over forest layers. -/
theorem central_direction_bound (m : ℕ) (hm : 2≤m) {q r s : ℝ}
    (hv : 9/40≤q*(1-q)) (hr : 0≤r) (hs : 0<s) (d : ℝ) :
    ‖periodIntegral (centralIntegrand m q d r)‖≤
      (s^2+(1-r)^2)/(2*s)*centralZero m q+(r/(2*s))*centralTwo m q := by
  have hv0 : 0<q*(1-q) := by linarith
  have hm0 : 0<((m-1:ℕ):ℝ) := by exact_mod_cast (show 0<m-1 by omega)
  have hb:=norm_period_le_majorant (mul_pos hm0 hv0)
    (c₃:=(m:ℝ)*(q*(1-q))*|1-2*q|/6) (c₄:=(m:ℝ)*(q*(1-q))/48)
    (c₀:=(s^2+(1-r)^2)/(2*s)) (c₂:=r/(2*s))
    (by positivity) (by positivity) (by positivity) (by positivity)
    (f:=centralIntegrand m q d r)
    (by unfold centralIntegrand multiplier BinomialCurvatureError.oscillation centeredBernoulliCharacteristic; fun_prop) ?_
  · dsimp only [centralZero,centralTwo]
    generalize hbdef : ((m-1:ℕ):ℝ)*(q*(1-q))=b at hb ⊢
    have hbpos : 0<b := hbdef ▸ mul_pos hm0 hv0
    have hbS : Real.sqrt b≠0 := (Real.sqrt_pos.mpr hbpos).ne'
    convert! hb using 1
    field_simp
    ring_nf
  · intro t ht
    have he:=centeredBinomialCharacteristic_error_bound m hv (abs_le.mpr ht)
    have hem : ‖centeredBernoulliCharacteristic q t^m-
        (Real.exp (-(m:ℝ)*(q*(1-q))*t^2/2):ℂ)‖≤
        majorant (((m-1:ℕ):ℝ)*(q*(1-q)))
          ((m:ℝ)*(q*(1-q))*|1-2*q|/6) ((m:ℝ)*(q*(1-q))/48) t := by
      apply he.trans_eq
      dsimp only [majorant]
      ring_nf
    rw [centralIntegrand,norm_mul,norm_mul,norm_oscillation,mul_one]
    have hslope : 0≤(s^2+(1-r)^2)/(2*s)+(r/(2*s))*t^2 := by positivity
    apply (mul_le_mul (multiplier_norm_young hr hs t) hem (norm_nonneg _) hslope).trans_eq
    ring_nf

theorem phase_step (a d t : ℝ) :
    GaussianCurvatureFourier.phase a (d+1) t=
      oscillation 1 t*GaussianCurvatureFourier.phase a d t := by
  unfold GaussianCurvatureFourier.phase BinomialCurvatureError.oscillation
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring_nf

theorem phase_direction (a d r t : ℝ) :
    GaussianCurvatureFourier.phase a d t-(r:ℂ)*GaussianCurvatureFourier.phase a (d+1) t=
      multiplier r t*GaussianCurvatureFourier.phase a d t := by
  rw [phase_step]
  unfold multiplier
  ring_nf

noncomputable def gaussianZero (a : ℝ) : ℝ :=
  Real.exp (-a*Real.pi^2/2)/(Real.pi^2*a)

noncomputable def gaussianTwo (a : ℝ) : ℝ :=
  (1/a+1/(Real.pi^2*a^2))*Real.exp (-a*Real.pi^2/2)

theorem zero_outside_bound {a : ℝ} (ha : 0<a) :
    (2*Real.pi)⁻¹*(∫t:ℝ in (Ioc (-Real.pi) Real.pi)ᶜ,Real.exp (-a*t^2/2))≤
      gaussianZero a := by
  rw [gaussian_zero_outside_eq ha Real.pi_pos.le]
  calc
    _ ≤ (2*Real.pi)⁻¹*(2*(Real.exp (-a*Real.pi^2/2)/(a*Real.pi))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (GaussianCurvatureTail.integral_zero_tail_le ha Real.pi_pos) (by norm_num)) (by positivity)
    _ = _ := by unfold gaussianZero; field_simp

theorem two_outside_bound {a : ℝ} (ha : 0<a) :
    (2*Real.pi)⁻¹*(∫t:ℝ in (Ioc (-Real.pi) Real.pi)ᶜ,t^2*Real.exp (-a*t^2/2))≤
      gaussianTwo a := by
  rw [GaussianCurvatureTail.integral_second_outside_eq ha]
  exact GaussianCurvatureTail.integral_second_tail_fourier_le ha

theorem gaussian_direction_tail {a r c₀ c₂ : ℝ} (ha : 0<a)
    (hc₀ : 0≤c₀) (hc₂ : 0≤c₂)
    (hmult : ∀t:ℝ,‖multiplier r t‖≤c₀+c₂*t^2) (d : ℝ) :
    ‖periodIntegral (fun t=>GaussianCurvatureFourier.phase a d t-
        (r:ℂ)*GaussianCurvatureFourier.phase a (d+1) t)-
      ((gaussianDensity a d-r*gaussianDensity a (d+1):ℝ):ℂ)‖≤
      c₀*gaussianZero a+c₂*gaussianTwo a := by
  let f:=fun t=>GaussianCurvatureFourier.phase a d t-
    (r:ℂ)*GaussianCurvatureFourier.phase a (d+1) t
  have hi0 : Integrable (GaussianCurvatureFourier.phase a d) := by
    simpa using GaussianCurvatureFourier.integrable_moment ha d 0
  have hi1 : Integrable (GaussianCurvatureFourier.phase a (d+1)) := by
    simpa using GaussianCurvatureFourier.integrable_moment ha (d+1) 0
  have hif : Integrable f := hi0.sub (hi1.const_mul (r:ℂ))
  have h0 : Integrable (fun t:ℝ=>Real.exp (-a*t^2/2)) := by
    simpa using GaussianCurvatureTail.integrable_real_moment ha 0
  have h2 := GaussianCurvatureTail.integrable_real_moment ha 2
  have hfull : ((gaussianDensity a d-r*gaussianDensity a (d+1):ℝ):ℂ)=
      (2*(Real.pi:ℂ))⁻¹*∫t:ℝ,f t := by
    dsimp [f]
    rw [integral_sub hi0 (hi1.const_mul _),integral_const_mul,mul_sub]
    rw [show (2*(Real.pi:ℂ))⁻¹*((r:ℂ)*∫t:ℝ,GaussianCurvatureFourier.phase a (d+1) t)=
      (r:ℂ)*((2*(Real.pi:ℂ))⁻¹*∫t:ℝ,GaussianCurvatureFourier.phase a (d+1) t) by ring_nf]
    rw [integral_gaussianDensity ha d,integral_gaussianDensity ha (d+1)]
    push_cast
    rfl
  have hd : (∫t:ℝ,f t)-(∫t in -Real.pi..Real.pi,f t)=
      ∫t:ℝ in (Ioc (-Real.pi) Real.pi)ᶜ,f t := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    exact (setIntegral_compl measurableSet_Ioc hif).symm
  rw [hfull,norm_sub_rev,periodIntegral,←mul_sub,hd,norm_mul,norm_normalizer]
  have hb : (∫t:ℝ in (Ioc (-Real.pi) Real.pi)ᶜ,‖f t‖)≤
      ∫t:ℝ in (Ioc (-Real.pi) Real.pi)ᶜ,
        c₀*Real.exp (-a*t^2/2)+c₂*(t^2*Real.exp (-a*t^2/2)) := by
    apply setIntegral_mono_on hif.norm.integrableOn
      ((h0.const_mul c₀).add (h2.const_mul c₂)).integrableOn measurableSet_Ioc.compl
    intro t _
    dsimp only [f]
    rw [phase_direction,norm_mul,GaussianCurvatureFourier.norm_phase]
    exact (mul_le_mul_of_nonneg_right (hmult t) (Real.exp_pos _).le).trans_eq (by dsimp; ring)
  calc
    _ ≤ (2*Real.pi)⁻¹*(∫t:ℝ in (Ioc (-Real.pi) Real.pi)ᶜ,‖f t‖) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ ≤ (2*Real.pi)⁻¹*(∫t:ℝ in (Ioc (-Real.pi) Real.pi)ᶜ,
        c₀*Real.exp (-a*t^2/2)+c₂*(t^2*Real.exp (-a*t^2/2))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = c₀*((2*Real.pi)⁻¹*∫t:ℝ in (Ioc (-Real.pi) Real.pi)ᶜ,Real.exp (-a*t^2/2))+
        c₂*((2*Real.pi)⁻¹*∫t:ℝ in (Ioc (-Real.pi) Real.pi)ᶜ,t^2*Real.exp (-a*t^2/2)) := by
      rw [integral_add (h0.const_mul c₀).integrableOn (h2.const_mul c₂).integrableOn,
        integral_const_mul,integral_const_mul]
      ring_nf
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (zero_outside_bound ha) hc₀)
      (mul_le_mul_of_nonneg_left (two_outside_bound ha) hc₂)


theorem actual_step (m : ℕ) (q d t : ℝ) :
    actualIntegrand m q (d+1) t=oscillation 1 t*actualIntegrand m q d t := by
  unfold actualIntegrand BinomialCurvatureError.oscillation
  rw [←mul_assoc,←Complex.exp_add]
  congr 2
  push_cast
  ring_nf

theorem actual_direction (m : ℕ) (q d r t : ℝ) :
    actualIntegrand m q d t-(r:ℂ)*actualIntegrand m q (d+1) t=
      multiplier r t*actualIntegrand m q d t := by
  rw [actual_step]
  unfold multiplier
  ring_nf

theorem difference_integrand (m : ℕ) (q d r t : ℝ) :
    (actualIntegrand m q d t-(r:ℂ)*actualIntegrand m q (d+1) t)-
      (GaussianCurvatureFourier.phase ((m:ℝ)*(q*(1-q))) d t-
        (r:ℂ)*GaussianCurvatureFourier.phase ((m:ℝ)*(q*(1-q))) (d+1) t)=
      centralIntegrand m q d r t := by
  rw [actual_direction,phase_direction,GaussianCurvatureFourier.phase_eq]
  unfold centralIntegrand actualIntegrand BinomialCurvatureError.oscillation
  ring_nf

theorem period_actual_direction (m : ℕ) (j : ℤ) (q r : ℝ) :
    periodIntegral (fun t=>actualIntegrand m q ((j:ℝ)-m*q) t-
      (r:ℂ)*actualIntegrand m q (((j:ℝ)-m*q)+1) t)=
      ((binomialMass m j q-r*binomialMass m (j+1) q:ℝ):ℂ) := by
  have hc (d:ℝ) : Continuous (actualIntegrand m q d) := by
    unfold actualIntegrand centeredBernoulliCharacteristic
    fun_prop
  rw [periodIntegral_sub (actualIntegrand m q ((j:ℝ)-m*q))
    (fun t=>(r:ℂ)*actualIntegrand m q (((j:ℝ)-m*q)+1) t) (hc _)
    (by exact continuous_const.mul (hc _))]
  have he (d:ℝ) : periodIntegral (fun t=>(r:ℂ)*actualIntegrand m q d t)=
      (r:ℂ)*periodIntegral (actualIntegrand m q d) := by
    unfold periodIntegral
    rw [intervalIntegral.integral_const_mul]
    ring_nf
  rw [he]
  change cutoffIntegral Real.pi (actualIntegrand m q ((j:ℝ)-m*q))-
    (r:ℂ)*cutoffIntegral Real.pi (actualIntegrand m q (((j:ℝ)-m*q)+1))=_
  have hcast : (((j+1:ℤ):ℝ)-m*q)=((j:ℝ)-m*q)+1 := by push_cast;ring_nf
  rw [←hcast,←binomialMass_eq_cutoff,←binomialMass_eq_cutoff]
  push_cast
  rfl

noncomputable def errorZero (m : ℕ) (q : ℝ) : ℝ :=
  centralZero m q+gaussianZero ((m:ℝ)*(q*(1-q)))

noncomputable def errorTwo (m : ℕ) (q : ℝ) : ℝ :=
  centralTwo m q+gaussianTwo ((m:ℝ)*(q*(1-q)))

/-- The free Young parameter is retained so that the same parameter can later
be used across all layers of an actual probability distribution. -/
theorem binomial_direction_young (m : ℕ) (hm : 2≤m) (j : ℤ) {q r s : ℝ}
    (hv : 9/40≤q*(1-q)) (hr : 0≤r) (hs : 0<s) :
    let a:=(m:ℝ)*(q*(1-q))
    let d:=(j:ℝ)-m*q
    |(binomialMass m j q-r*binomialMass m (j+1) q)-
      (gaussianDensity a d-r*gaussianDensity a (d+1))|≤
      (s^2+(1-r)^2)/(2*s)*errorZero m q+(r/(2*s))*errorTwo m q := by
  dsimp only
  let a:=(m:ℝ)*(q*(1-q))
  let d:=(j:ℝ)-m*q
  have hv0 : 0<q*(1-q) := by linarith
  have hm0 : 0<(m:ℝ) := by exact_mod_cast (show 0<m by omega)
  have ha : 0<a := mul_pos hm0 hv0
  let f:=fun t=>actualIntegrand m q d t-(r:ℂ)*actualIntegrand m q (d+1) t
  let g:=fun t=>GaussianCurvatureFourier.phase a d t-
    (r:ℂ)*GaussianCurvatureFourier.phase a (d+1) t
  have hf : Continuous f := by
    dsimp [f,actualIntegrand,centeredBernoulliCharacteristic]
    fun_prop
  have hg : Continuous g := by
    dsimp [g]
    exact (GaussianCurvatureFourier.continuous_phase a d).sub
      (continuous_const.mul (GaussianCurvatureFourier.continuous_phase a (d+1)))
  have hcentral : ‖periodIntegral f-periodIntegral g‖≤
      (s^2+(1-r)^2)/(2*s)*centralZero m q+(r/(2*s))*centralTwo m q := by
    rw [←periodIntegral_sub _ _ hf hg]
    have he : (fun t=>f t-g t)=centralIntegrand m q d r := by
      funext t
      exact difference_integrand m q d r t
    rw [he]
    exact central_direction_bound m hm hv hr hs d
  have htail:=gaussian_direction_tail ha
    (c₀:=(s^2+(1-r)^2)/(2*s)) (c₂:=r/(2*s))
    (by positivity) (by positivity) (multiplier_norm_young hr hs) d
  have ht:=norm_sub_le_norm_sub_add_norm_sub (periodIntegral f) (periodIntegral g)
    ((gaussianDensity a d-r*gaussianDensity a (d+1):ℝ):ℂ)
  have hb:=ht.trans (add_le_add hcentral htail)
  have hpf : periodIntegral f=((binomialMass m j q-r*binomialMass m (j+1) q:ℝ):ℂ) :=
    period_actual_direction m j q r
  rw [hpf,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at hb
  apply hb.trans_eq
  dsimp only [errorZero,errorTwo,a]
  ring_nf


theorem errorZero_pos (m : ℕ) (hm : 2≤m) {q : ℝ}
    (hv : 0<q*(1-q)) : 0<errorZero m q := by
  have hm0 : 0<(m:ℝ) := by exact_mod_cast (show 0<m by omega)
  have hm1 : 0<((m-1:ℕ):ℝ) := by exact_mod_cast (show 0<m-1 by omega)
  dsimp [errorZero,centralZero,gaussianZero]
  positivity

theorem errorTwo_pos (m : ℕ) (hm : 2≤m) {q : ℝ}
    (hv : 0<q*(1-q)) : 0<errorTwo m q := by
  have hm0 : 0<(m:ℝ) := by exact_mod_cast (show 0<m by omega)
  have hm1 : 0<((m-1:ℕ):ℝ) := by exact_mod_cast (show 0<m-1 by omega)
  dsimp [errorTwo,centralTwo,gaussianTwo]
  positivity

/-- The reverse adjacent direction has exactly the same two moment costs. -/
theorem binomial_reverse_direction_young (m : ℕ) (hm : 2≤m) (j : ℤ) {q r s : ℝ}
    (hv : 9/40≤q*(1-q)) (hr : 0<r) (hs : 0<s) :
    let a:=(m:ℝ)*(q*(1-q))
    let d:=(j:ℝ)-m*q
    |(binomialMass m j q-r*binomialMass m (j-1) q)-
      (gaussianDensity a d-r*gaussianDensity a (d-1))|≤
      (s^2+(1-r)^2)/(2*s)*errorZero m q+(r/(2*s))*errorTwo m q := by
  dsimp only
  have h:=binomial_direction_young m hm (j-1) hv (r:=1/r) (s:=s/r)
    (by positivity) (by positivity)
  dsimp only at h
  have hd : (((j-1:ℤ):ℝ)-m*q)=((j:ℝ)-m*q)-1 := by push_cast;ring_nf
  rw [sub_add_cancel,hd,sub_add_cancel] at h
  have he : (binomialMass m j q-r*binomialMass m (j-1) q)-
      (gaussianDensity ((m:ℝ)*(q*(1-q))) ((j:ℝ)-m*q)-
        r*gaussianDensity ((m:ℝ)*(q*(1-q))) (((j:ℝ)-m*q)-1))=
      -r*((binomialMass m (j-1) q-(1/r)*binomialMass m j q)-
        (gaussianDensity ((m:ℝ)*(q*(1-q))) (((j:ℝ)-m*q)-1)-
          (1/r)*gaussianDensity ((m:ℝ)*(q*(1-q))) ((j:ℝ)-m*q))) := by
    field_simp
    ring_nf
  rw [he,abs_mul,abs_neg,abs_of_pos hr]
  apply (mul_le_mul_of_nonneg_left h hr.le).trans_eq
  field_simp
  ring_nf

theorem optimize_direction {E₀ E₂ r Z : ℝ} (hE₀ : 0<E₀) (hE₂ : 0<E₂)
    (hr : 0≤r)
    (h : ∀s>0,Z≤(s^2+(1-r)^2)/(2*s)*E₀+(r/(2*s))*E₂) :
    Z≤Real.sqrt (E₀*((1-r)^2*E₀+r*E₂)) := by
  have hB : 0<(1-r)^2*E₀+r*E₂ := by
    rcases hr.eq_or_lt with he|he
    · rw [←he]
      simpa using hE₀
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg _) hE₀.le) (mul_pos he hE₂)
  apply young_optimize hE₀ hB
  intro s hs
  apply (h s hs).trans_eq
  ring_nf

/-- Degenerate zero-mass cases are allowed when averaging the Fourier measure. -/
theorem young_optimize_nonneg {A B Z : ℝ} (hA : 0≤A) (hB : 0≤B)
    (h : ∀s>0,Z≤(s^2*A+B)/(2*s)) : Z≤Real.sqrt (A*B) := by
  rcases hA.eq_or_lt with ha|ha
  · rw [←ha,zero_mul,Real.sqrt_zero]
    by_contra hn
    have hZ : 0<Z := lt_of_not_ge hn
    rcases hB.eq_or_lt with hb|hb
    · have hh:=h 1 (by norm_num)
      rw [←ha,←hb] at hh
      norm_num at hh
      exact (not_le_of_gt hZ) hh
    · have hh:=h (B/Z) (div_pos hb hZ)
      have he : ((B/Z)^2*A+B)/(2*(B/Z))=Z/2 := by rw [←ha];field_simp;ring_nf
      rw [he] at hh
      linarith
  · rcases hB.eq_or_lt with hb|hb
    · rw [←hb,mul_zero,Real.sqrt_zero]
      by_contra hn
      have hZ : 0<Z := lt_of_not_ge hn
      have hh:=h (Z/A) (div_pos hZ ha)
      have he : ((Z/A)^2*A+B)/(2*(Z/A))=Z/2 := by rw [←hb];field_simp;ring_nf
      rw [he] at hh
      linarith
    · exact young_optimize ha hb h

theorem optimize_direction_nonneg {E₀ E₂ r Z : ℝ} (hE₀ : 0≤E₀) (hE₂ : 0≤E₂)
    (hr : 0≤r)
    (h : ∀s>0,Z≤(s^2+(1-r)^2)/(2*s)*E₀+(r/(2*s))*E₂) :
    Z≤Real.sqrt (E₀*((1-r)^2*E₀+r*E₂)) := by
  apply young_optimize_nonneg hE₀ (by positivity)
  intro s hs
  apply (h s hs).trans_eq
  ring_nf

/-- Actual binomial-to-Gaussian directional error, with a common Fourier
measure supplying both moments. Valid for every integer index, including
indices outside binomial support. -/
theorem binomial_direction_error (m : ℕ) (hm : 2≤m) (j : ℤ) {q r : ℝ}
    (hv : 9/40≤q*(1-q)) (hr : 0≤r) :
    let a:=(m:ℝ)*(q*(1-q))
    let d:=(j:ℝ)-m*q
    |(binomialMass m j q-r*binomialMass m (j+1) q)-
      (gaussianDensity a d-r*gaussianDensity a (d+1))|≤
      Real.sqrt (errorZero m q*((1-r)^2*errorZero m q+r*errorTwo m q)) := by
  apply optimize_direction (errorZero_pos m hm (by linarith))
    (errorTwo_pos m hm (by linarith)) hr
  intro s hs
  exact binomial_direction_young m hm j hv hr hs

theorem binomial_reverse_direction_error (m : ℕ) (hm : 2≤m) (j : ℤ) {q r : ℝ}
    (hv : 9/40≤q*(1-q)) (hr : 0<r) :
    let a:=(m:ℝ)*(q*(1-q))
    let d:=(j:ℝ)-m*q
    |(binomialMass m j q-r*binomialMass m (j-1) q)-
      (gaussianDensity a d-r*gaussianDensity a (d-1))|≤
      Real.sqrt (errorZero m q*((1-r)^2*errorZero m q+r*errorTwo m q)) := by
  apply optimize_direction (errorZero_pos m hm (by linarith))
    (errorTwo_pos m hm (by linarith)) hr.le
  intro s hs
  exact binomial_reverse_direction_young m hm j hv hr hs

#print axioms multiplier_norm_young
#print axioms young_optimize
#print axioms integral_second_majorant
#print axioms central_direction_bound
#print axioms gaussian_direction_tail
#print axioms binomial_direction_young
#print axioms binomial_direction_error
#print axioms binomial_reverse_direction_error
end ForestUnimodality.BinomialDirectionalError
