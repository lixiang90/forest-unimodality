import ForestUnimodality.NegativePowerLayerBudget

/-! Exact shifted free-count moments on the original hard-core layer law.
The deterministic shift never changes the probability space or tail exponent. -/
namespace ForestUnimodality.ShiftedLayerMoments
open NegativePowerLayerBudget
variable {V : Type*} [DecidableEq V]

noncomputable def ratio (m c : ℝ) (M : ℕ) : ℝ := ((M:ℝ)+c)/(m+c)
noncomputable def offset (z m c k v : ℝ) (j M : ℕ) : ℝ :=
  (k-binomialLayerMean j M z)/Real.sqrt (v*(m+c))
noncomputable def quadratic (H L a B y w : ℝ) : ℝ :=
  H+L*(y-1)-a*w^2-B*(y-1)^2

theorem centered_ratio_expectation (G : SimpleGraph V) (S I : Finset V)
    (hIS : I⊆S) (hI : G.IsIndepSet (I:Set V)) {z m c : ℝ}
    (hz : 0≤z) (hm : m=hardCoreAvailableMean G S I z) (hm0 : 0<m) (hc : 0≤c) :
    hardCoreLayerExpectation G S I z (fun _ M=>ratio m c M-1)=0 := by
  have hmc : m+c≠0 := ne_of_gt (by linarith)
  have hmean : hardCoreLayerExpectation G S I z (fun _ M=>(M:ℝ))=m := by
    simpa only [hardCoreLayerExpectation,hardCoreAvailableMean] using hm.symm
  have he (M : ℕ) : ratio m c M-1=(1/(m+c))*((M:ℝ)-m) := by unfold ratio; field_simp; ring
  simp_rw [he]
  rw [layer_const_mul,layer_sub,hmean,layer_const G S I hIS hI hz]
  ring

theorem centered_ratio_square (G : SimpleGraph V) (S I : Finset V)
    {z m c : ℝ} (hm : m=hardCoreAvailableMean G S I z) (hm0 : 0<m) (hc : 0≤c) :
    hardCoreLayerExpectation G S I z (fun _ M=>(ratio m c M-1)^2)=
      hardCoreAvailableVariance G S I z/(m+c)^2 := by
  have hmc : m+c≠0 := ne_of_gt (by linarith)
  have he (M : ℕ) : (ratio m c M-1)^2=(1/(m+c)^2)*((M:ℝ)-m)^2 := by
    unfold ratio; field_simp; ring
  simp_rw [he]
  rw [layer_const_mul,hm]
  change (1/_)*hardCoreAvailableVariance G S I z=_
  ring

theorem offset_square (G : SimpleGraph V) (S I : Finset V)
    (hIS : I⊆S) (hI : G.IsIndepSet (I:Set V)) {z m c k v : ℝ}
    (hz : 0<z) (hm : m=hardCoreAvailableMean G S I z) (hm0 : 0<m) (hc : 0≤c)
    (hmean : hardCoreMean G S z=k) (hv : 0<v) :
    hardCoreLayerExpectation G S I z (fun j M=>(offset z m c k v j M)^2)=
      (hardCoreVariance G S z-(z/(1+z))*(1-z/(1+z))*m)/(v*(m+c)) := by
  have hmc : 0<m+c := by linarith
  have he (j M : ℕ) : (offset z m c k v j M)^2=
      (1/(v*(m+c)))*(k-binomialLayerMean j M z)^2 := by
    unfold offset
    rw [div_pow,Real.sq_sqrt (mul_pos hv hmc).le]
    ring
  simp_rw [he]
  rw [layer_const_mul,hardCoreLayerExpectation_centered_sq G S I hIS hI hz hmean,hm]
  ring

theorem quadratic_expectation (G : SimpleGraph V) (S I : Finset V)
    (hIS : I⊆S) (hI : G.IsIndepSet (I:Set V)) {z m c k v : ℝ}
    (hz : 0<z) (hm : m=hardCoreAvailableMean G S I z) (hm0 : 0<m) (hc : 0≤c)
    (hmean : hardCoreMean G S z=k) (hv : 0<v) (H L a B : ℝ) :
    hardCoreLayerExpectation G S I z (fun j M=>quadratic H L a B
      (ratio m c M) (offset z m c k v j M))=
      H-a*((hardCoreVariance G S z-(z/(1+z))*(1-z/(1+z))*m)/(v*(m+c)))-
        B*(hardCoreAvailableVariance G S I z/(m+c)^2) := by
  unfold quadratic
  rw [layer_sub,layer_sub,layer_add,layer_const G S I hIS hI hz.le,
    layer_const_mul,layer_const_mul,layer_const_mul,
    centered_ratio_expectation G S I hIS hI hz.le hm hm0 hc,
    centered_ratio_square G S I hm hm0 hc,offset_square G S I hIS hI hz hm hm0 hc hmean hv]
  ring

theorem quadratic_expectation_lower (G : SimpleGraph V) (S I : Finset V)
    (hIS : I⊆S) (hI : G.IsIndepSet (I:Set V)) {z m c k v H L a B R D : ℝ}
    (hz : 0<z) (hm : m=hardCoreAvailableMean G S I z) (hm0 : 0<m) (hc : 0≤c)
    (hmean : hardCoreMean G S z=k) (hv : 0<v) (ha : 0≤a) (hB : 0≤B)
    (hR : 0≤R) (hD : 0≤D)
    (hvarL : hardCoreVariance G S z-(z/(1+z))*(1-z/(1+z))*m≤R*(v*m))
    (hvarM : hardCoreAvailableVariance G S I z≤D*m) :
    H-a*R-B*D/m≤hardCoreLayerExpectation G S I z (fun j M=>quadratic H L a B
      (ratio m c M) (offset z m c k v j M)) := by
  have hmc : 0<m+c := by linarith
  have hL : (hardCoreVariance G S z-(z/(1+z))*(1-z/(1+z))*m)/(v*(m+c))≤R := by
    apply (div_le_iff₀ (mul_pos hv hmc)).mpr
    exact hvarL.trans (by nlinarith [mul_nonneg (mul_nonneg hR hv.le) hc])
  have hM : hardCoreAvailableVariance G S I z/(m+c)^2≤D/m := by
    apply (div_le_iff₀ (sq_pos_of_pos hmc)).mpr
    apply hvarM.trans
    have hsq : m^2≤(m+c)^2 := by nlinarith
    calc
      D*m=(D/m)*m^2 := by field_simp
      _≤(D/m)*(m+c)^2 := mul_le_mul_of_nonneg_left hsq (div_nonneg hD hm0.le)
  rw [quadratic_expectation G S I hIS hI hz hm hm0 hc hmean hv]
  have h1:=mul_le_mul_of_nonneg_left hL ha
  have h2:=mul_le_mul_of_nonneg_left hM hB
  simp only [mul_div_assoc] at h1 h2 ⊢
  linarith

theorem ratio_good {m c alpha : ℝ} {M : ℕ} (hm : 0<m) (hc : 0≤c)
    (ha : alpha≤1) (hM : alpha*m≤(M:ℝ)) : alpha≤ratio m c M := by
  unfold ratio
  apply (le_div_iff₀ (by linarith : 0<m+c)).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) hc]

theorem ratio_below_imp {m c t : ℝ} {M : ℕ} (hm : 0<m) (hc : 0≤c)
    (ht : t≤1) (hM : ratio m c M<t) : (M:ℝ)<t*m := by
  unfold ratio at hM
  have hh := (div_lt_iff₀ (by linarith : 0<m+c)).mp hM
  nlinarith [mul_nonneg (sub_nonneg.mpr ht) hc]

theorem lowerTail_le_original (G : SimpleGraph V) (S I : Finset V)
    {z m c t : ℝ} (hz : 0≤z) (hm : 0<m) (hc : 0≤c) (ht : t≤1) :
    hardCoreLayerExpectation G S I z (fun _ M=>if ratio m c M<t then 1 else 0)≤
      hardCoreAvailableLowerTail G S I z (t*m) := by
  unfold hardCoreAvailableLowerTail
  apply layer_mono G S I hz
  intro j M
  by_cases hh : ratio m c M<t
  · simp only [if_pos hh,if_pos (ratio_below_imp hm hc ht hh),le_refl]
  · simp only [if_neg hh]
    split_ifs <;> norm_num

theorem ratio_bad_upper {m c cmax alpha : ℝ} {M : ℕ}
    (hm : 0<m) (hc : 0≤c) (hcc : c≤cmax) (ha : alpha≤1) (hM : (M:ℝ)<alpha*m) :
    ratio m c M≤(alpha*m+cmax)/(m+cmax) := by
  have hcm : 0<m+c := by linarith
  have hmax : 0<m+cmax := by linarith
  have h1 : ratio m c M≤(alpha*m+c)/(m+c) := by
    unfold ratio; exact div_le_div_of_nonneg_right (by linarith) hcm.le
  apply h1.trans
  apply (div_le_div_iff₀ hcm hmax).mpr
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr ha) hm.le) (sub_nonneg.mpr hcc)]

theorem quadratic_nonpos_below {H L a B t y w : ℝ}
    (hL : 0≤L) (ha : 0≤a) (hB : 0≤B) (ht : t≤1) (hy : y≤t)
    (hpoint : H+L*(t-1)-B*(t-1)^2≤0) : quadratic H L a B y w≤0 := by
  have hp : 0≤(t-y)*(L+B*(2-t-y)) := by
    apply mul_nonneg (sub_nonneg.mpr hy)
    exact add_nonneg hL (mul_nonneg hB (by linarith))
  have hw:=mul_nonneg ha (sq_nonneg w)
  unfold quadratic
  nlinarith

#print axioms quadratic_expectation
#print axioms quadratic_expectation_lower
#print axioms ratio_below_imp
#print axioms ratio_bad_upper
end ForestUnimodality.ShiftedLayerMoments
