import ForestUnimodality.GaussianCurvatureFourier

/-! Explicit finite Gaussian tail estimates, with the cutoff retained.
The tail costs follow from integrable derivatives and a Mills comparison. -/
namespace ForestUnimodality.GaussianCurvatureTail
open Real Set MeasureTheory

theorem integrable_real_moment {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Integrable (fun t : ℝ => t ^ n * Real.exp (-a * t ^ 2 / 2)) := by
  have hi := integrable_rpow_mul_exp_neg_mul_sq (by positivity : 0 < a / 2)
    (s := (n : ℝ)) (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n))
  simp only [Real.rpow_natCast] at hi
  convert hi using 1
  funext t
  congr 2
  ring

theorem integral_first_tail {a : ℝ} (ha : 0 < a) (r : ℝ) :
    (∫ t : ℝ in Ioi r, t * Real.exp (-a * t ^ 2 / 2)) =
      Real.exp (-a * r ^ 2 / 2) / a := by
  have h0 : Integrable (fun t : ℝ => Real.exp (-a * t ^ 2 / 2)) := by
    simpa using integrable_real_moment ha 0
  have h1 : Integrable (fun t : ℝ => t * Real.exp (-a * t ^ 2 / 2)) := by
    simpa using integrable_real_moment ha 1
  have hd (t : ℝ) : HasDerivAt (fun t => -Real.exp (-a * t ^ 2 / 2) / a)
      (t * Real.exp (-a * t ^ 2 / 2)) t := by
    convert! ((((((hasDerivAt_id t).pow 2).const_mul (-a)).div_const 2).exp).neg).div_const a using 1
    simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
      pow_one, mul_one]
    field_simp
  have hf := h0.neg.div_const a
  have hz := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
    (fun t (_ : t ∈ Ioi r) => hd t) h1.integrableOn hf.integrableOn
  have he := integral_Ioi_of_hasDerivAt_of_tendsto' (fun t (_ : t ∈ Ici r) => hd t)
    h1.integrableOn hz
  simpa only [zero_sub, neg_div, neg_neg] using he

theorem integral_second_tail_relation {a : ℝ} (ha : 0 < a) (r : ℝ) :
    a * (∫ t : ℝ in Ioi r, t ^ 2 * Real.exp (-a * t ^ 2 / 2)) =
      r * Real.exp (-a * r ^ 2 / 2) + (∫ t : ℝ in Ioi r, Real.exp (-a * t ^ 2 / 2)) := by
  have h0 : Integrable (fun t : ℝ => Real.exp (-a * t ^ 2 / 2)) := by
    simpa using integrable_real_moment ha 0
  have h1 : Integrable (fun t : ℝ => t * Real.exp (-a * t ^ 2 / 2)) := by
    simpa using integrable_real_moment ha 1
  have h2 := integrable_real_moment ha 2
  have hd (t : ℝ) : HasDerivAt (fun t => t * Real.exp (-a * t ^ 2 / 2))
      (Real.exp (-a * t ^ 2 / 2) - a * (t ^ 2 * Real.exp (-a * t ^ 2 / 2))) t := by
    convert! (hasDerivAt_id t).mul
      (((((hasDerivAt_id t).pow 2).const_mul (-a)).div_const 2).exp) using 1
    simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, one_mul]
    ring
  have hi := h0.sub (h2.const_mul a)
  have hz := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
    (fun t (_ : t ∈ Ioi r) => hd t) hi.integrableOn h1.integrableOn
  have he := integral_Ioi_of_hasDerivAt_of_tendsto' (fun t (_ : t ∈ Ici r) => hd t)
    hi.integrableOn hz
  rw [integral_sub h0.integrableOn (h2.const_mul a).integrableOn, integral_const_mul] at he
  linarith

theorem integral_zero_tail_le {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (∫ t : ℝ in Ioi r, Real.exp (-a * t ^ 2 / 2)) ≤
      Real.exp (-a * r ^ 2 / 2) / (a * r) := by
  have h0 : Integrable (fun t : ℝ => Real.exp (-a * t ^ 2 / 2)) := by
    simpa using integrable_real_moment ha 0
  have h1 : Integrable (fun t : ℝ => t * Real.exp (-a * t ^ 2 / 2)) := by
    simpa using integrable_real_moment ha 1
  have he := setIntegral_mono_on h0.integrableOn (h1.div_const r).integrableOn
    measurableSet_Ioi (fun t (ht : t ∈ Ioi r) => show
      Real.exp (-a * t ^ 2 / 2) ≤ t * Real.exp (-a * t ^ 2 / 2) / r from by
        apply (le_div_iff₀ hr).mpr
        have htr : r < t := ht
        nlinarith [Real.exp_pos (-a * t ^ 2 / 2)])
  rw [integral_div, integral_first_tail ha r] at he
  calc
    _ ≤ Real.exp (-a * r ^ 2 / 2) / a / r := he
    _ = _ := by ring

theorem integral_second_tail_le {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (∫ t : ℝ in Ioi r, t ^ 2 * Real.exp (-a * t ^ 2 / 2)) ≤
      (r / a + 1 / (a ^ 2 * r)) * Real.exp (-a * r ^ 2 / 2) := by
  have he := integral_second_tail_relation ha r
  have hb := integral_zero_tail_le ha hr
  apply (mul_le_mul_iff_of_pos_left ha).mp
  rw [he]
  have hid : a * ((r / a + 1 / (a ^ 2 * r)) * Real.exp (-a * r ^ 2 / 2)) =
      r * Real.exp (-a * r ^ 2 / 2) + Real.exp (-a * r ^ 2 / 2) / (a * r) := by
    field_simp
  rw [hid]
  linarith

theorem integral_second_tail_fourier_le {a : ℝ} (ha : 0 < a) :
    (2 * Real.pi)⁻¹ * (2 * ∫ t : ℝ in Ioi Real.pi, t ^ 2 * Real.exp (-a * t ^ 2 / 2)) ≤
      (1 / a + 1 / (Real.pi ^ 2 * a ^ 2)) * Real.exp (-a * Real.pi ^ 2 / 2) := by
  calc
    _ = Real.pi⁻¹ * (∫ t : ℝ in Ioi Real.pi, t ^ 2 * Real.exp (-a * t ^ 2 / 2)) := by
      have hc : (2 * Real.pi)⁻¹ * 2 = Real.pi⁻¹ := by field_simp
      rw [← mul_assoc, hc]
    _ ≤ Real.pi⁻¹ * ((Real.pi / a + 1 / (a ^ 2 * Real.pi)) *
        Real.exp (-a * Real.pi ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_left (integral_second_tail_le ha Real.pi_pos) (by positivity)
    _ = _ := by field_simp

theorem integral_second_outside_eq {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ in (Ioc (-Real.pi) Real.pi)ᶜ, t ^ 2 * Real.exp (-a * t ^ 2 / 2)) =
      2 * ∫ t : ℝ in Ioi Real.pi, t ^ 2 * Real.exp (-a * t ^ 2 / 2) := by
  have hi := integrable_real_moment ha 2
  rw [compl_Ioc, setIntegral_union (Iic_disjoint_Ioi (by linarith [Real.pi_pos]))
    measurableSet_Ioi hi.integrableOn hi.integrableOn]
  have he := integral_comp_neg_Iic (-Real.pi)
    (fun t : ℝ => t ^ 2 * Real.exp (-a * t ^ 2 / 2))
  simp only [neg_sq, neg_neg] at he
  rw [he]
  ring

/-- The finite-period truncation of the exact Gaussian curvature integral.
The variance `s` may exceed the variance `a` used to price the tail. -/
theorem norm_full_sub_period_le {a s : ℝ} (ha : 0 < a) (has : a ≤ s) (d : ℝ) :
    ‖(2 * (Real.pi : ℂ))⁻¹ *
      ((∫ t : ℝ, (t : ℂ) ^ 2 * GaussianCurvatureFourier.phase s d t) -
        ∫ t in -Real.pi..Real.pi, (t : ℂ) ^ 2 * GaussianCurvatureFourier.phase s d t)‖ ≤
      (1 / a + 1 / (Real.pi ^ 2 * a ^ 2)) * Real.exp (-a * Real.pi ^ 2 / 2) := by
  have hs : 0 < s := ha.trans_le has
  have hi := GaussianCurvatureFourier.integrable_moment hs d 2
  have hia := integrable_real_moment ha 2
  have hd : (∫ t : ℝ, (t : ℂ) ^ 2 * GaussianCurvatureFourier.phase s d t) -
      (∫ t in -Real.pi..Real.pi, (t : ℂ) ^ 2 * GaussianCurvatureFourier.phase s d t) =
      ∫ t : ℝ in (Ioc (-Real.pi) Real.pi)ᶜ,
        (t : ℂ) ^ 2 * GaussianCurvatureFourier.phase s d t := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    exact (setIntegral_compl measurableSet_Ioc hi).symm
  rw [hd, norm_mul]
  have hn : ‖(2 * (Real.pi : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
    simp [norm_inv, Complex.norm_real, abs_of_pos Real.pi_pos]
  rw [hn]
  have hb : (∫ t : ℝ in (Ioc (-Real.pi) Real.pi)ᶜ,
      ‖(t : ℂ) ^ 2 * GaussianCurvatureFourier.phase s d t‖) ≤
      ∫ t : ℝ in (Ioc (-Real.pi) Real.pi)ᶜ, t ^ 2 * Real.exp (-a * t ^ 2 / 2) := by
    apply setIntegral_mono_on hi.norm.integrableOn hia.integrableOn measurableSet_Ioc.compl
    intro t ht
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      GaussianCurvatureFourier.norm_phase]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg t)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr has) (sq_nonneg t)]
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (∫ t : ℝ in (Ioc (-Real.pi) Real.pi)ᶜ,
        ‖(t : ℂ) ^ 2 * GaussianCurvatureFourier.phase s d t‖) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ ≤ (2 * Real.pi)⁻¹ * (∫ t : ℝ in (Ioc (-Real.pi) Real.pi)ᶜ,
        t ^ 2 * Real.exp (-a * t ^ 2 / 2)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (2 * Real.pi)⁻¹ * (2 * ∫ t : ℝ in Ioi Real.pi,
        t ^ 2 * Real.exp (-a * t ^ 2 / 2)) := by rw [integral_second_outside_eq ha]
    _ ≤ _ := integral_second_tail_fourier_le ha

#print axioms integral_first_tail
#print axioms integral_second_tail_relation
#print axioms integral_second_tail_fourier_le
#print axioms norm_full_sub_period_le
end ForestUnimodality.GaussianCurvatureTail
