import ForestUnimodality.BinomialDirectionalError
import ForestUnimodality.NegativePowerLayerBudget
import ForestUnimodality.DirectionalErrorEnvelope

/-! A common Fourier error measure is averaged over the original joint graph
layer law. In particular the two moments are not maximized on different laws. -/
namespace ForestUnimodality.DirectionalErrorLayerBudget
open BinomialDirectionalError BinomialPointMassError NegativePowerLayerBudget

noncomputable def pointDifference (reverse : Bool) (M : ℕ) (q r : ℝ) (k : ℤ) : ℝ :=
  let d:=(k:ℝ)-M*q
  let a:=(M:ℝ)*(q*(1-q))
  if reverse then
    (binomialMass M k q-r*binomialMass M (k-1) q)-
      (gaussianDensity a d-r*gaussianDensity a (d-1))
  else
    (binomialMass M k q-r*binomialMass M (k+1) q)-
      (gaussianDensity a d-r*gaussianDensity a (d+1))

theorem pointDifference_young (reverse : Bool) (M : ℕ) (hM : 2≤M) (k : ℤ)
    {q r s : ℝ} (hv : 9/40≤q*(1-q)) (hr : 0<r) (hs : 0<s) :
    |pointDifference reverse M q r k|≤
      (s^2+(1-r)^2)/(2*s)*errorZero M q+(r/(2*s))*errorTwo M q := by
  cases reverse with
  | false => exact binomial_direction_young M hM k hv hr.le hs
  | true => exact binomial_reverse_direction_young M hM k hv hr hs

variable {V : Type*} [DecidableEq V]

theorem abs_layer_le (G : SimpleGraph V) (S I : Finset V) {z : ℝ} (hz : 0≤z)
    (f : ℕ→ℕ→ℝ) :
    |hardCoreLayerExpectation G S I z f|≤
      hardCoreLayerExpectation G S I z (fun j M=>|f j M|) := by
  apply abs_le.mpr
  constructor
  · have h:=layer_mono G S I hz (fun j M=>(-1)*|f j M|) f
      (fun j M=>by simpa only [neg_one_mul] using neg_abs_le (f j M))
    rw [layer_const_mul,neg_one_mul] at h
    exact h
  · exact layer_mono G S I hz f (fun j M=>|f j M|) (fun j M=>le_abs_self _)

noncomputable def momentZero (G : SimpleGraph V) (S I : Finset V) (z q cutoff : ℝ) : ℝ :=
  hardCoreLayerExpectation G S I z (fun _ M=>if cutoff≤(M:ℝ) then errorZero M q else 0)

noncomputable def momentTwo (G : SimpleGraph V) (S I : Finset V) (z q cutoff : ℝ) : ℝ :=
  hardCoreLayerExpectation G S I z (fun _ M=>if cutoff≤(M:ℝ) then errorTwo M q else 0)

noncomputable def averagedDifference (G : SimpleGraph V) (S I : Finset V)
    (z q cutoff r : ℝ) (k : ℤ) (reverse : Bool) : ℝ :=
  hardCoreLayerExpectation G S I z (fun j M=>if cutoff≤(M:ℝ) then
    pointDifference reverse M q r (k-(j:ℤ)) else 0)

theorem retained_ge_two {cutoff : ℝ} (hc : 1<cutoff) {M : ℕ}
    (hM : cutoff≤(M:ℝ)) : 2≤M := by
  have hm : (1:ℝ)<(M:ℝ) := hc.trans_le hM
  have : 1<M := by exact_mod_cast hm
  omega

theorem moments_nonneg (G : SimpleGraph V) (S I : Finset V) {z q cutoff : ℝ}
    (hz : 0≤z) (hv : 0<q*(1-q)) (hc : 1<cutoff) :
    0≤momentZero G S I z q cutoff ∧ 0≤momentTwo G S I z q cutoff := by
  have h0 : hardCoreLayerExpectation G S I z (fun _ _=>0)=0 := by
    simp [hardCoreLayerExpectation]
  constructor
  · rw [←h0]
    exact layer_mono G S I hz _ _ (fun j M=>by
      by_cases hM : cutoff≤(M:ℝ)
      · simpa only [if_pos hM] using (errorZero_pos M (retained_ge_two hc hM) hv).le
      · simp [hM])
  · rw [←h0]
    exact layer_mono G S I hz _ _ (fun j M=>by
      by_cases hM : cutoff≤(M:ℝ)
      · simpa only [if_pos hM] using (errorTwo_pos M (retained_ge_two hc hM) hv).le
      · simp [hM])

theorem averaged_young (G : SimpleGraph V) (S I : Finset V)
    {z q cutoff r s : ℝ} (hz : 0≤z) (hv : 9/40≤q*(1-q))
    (hc : 1<cutoff) (hr : 0<r) (hs : 0<s) (k : ℤ) (reverse : Bool) :
    |averagedDifference G S I z q cutoff r k reverse|≤
      (s^2+(1-r)^2)/(2*s)*momentZero G S I z q cutoff+
        (r/(2*s))*momentTwo G S I z q cutoff := by
  apply (abs_layer_le G S I hz _).trans
  have hm:=layer_mono G S I hz
    (fun j M=>|if cutoff≤(M:ℝ) then pointDifference reverse M q r (k-j) else 0|)
    (fun _ M=>(s^2+(1-r)^2)/(2*s)*(if cutoff≤(M:ℝ) then errorZero M q else 0)+
      (r/(2*s))*(if cutoff≤(M:ℝ) then errorTwo M q else 0)) (by
    intro j M
    by_cases hM : cutoff≤(M:ℝ)
    · simpa only [if_pos hM] using
        pointDifference_young reverse M (retained_ge_two hc hM) (k-j) hv hr hs
    · simp [hM])
  rw [layer_add,layer_const_mul,layer_const_mul] at hm
  exact hm

/-- Optimizing is done after averaging, so the zeroth and second moment
budgets belong to exactly the same actual hard-core law. -/
theorem actual_averaged_error (G : SimpleGraph V) (S I : Finset V)
    {z q cutoff r : ℝ} (hz : 0≤z) (hv : 9/40≤q*(1-q))
    (hc : 1<cutoff) (hr : 0<r) (k : ℤ) (reverse : Bool) :
    |averagedDifference G S I z q cutoff r k reverse|≤
      Real.sqrt (momentZero G S I z q cutoff*
        ((1-r)^2*momentZero G S I z q cutoff+r*momentTwo G S I z q cutoff)) := by
  obtain ⟨h0,h2⟩:=moments_nonneg G S I (q:=q) hz (by linarith) hc
  apply optimize_direction_nonneg h0 h2 hr.le
  intro s hs
  exact averaged_young G S I hz hv hc hr hs k reverse

theorem actual_averaged_error_of_budgets (G : SimpleGraph V) (S I : Finset V)
    {z q cutoff r E₀ E₂ : ℝ} (hz : 0≤z) (hv : 9/40≤q*(1-q))
    (hc : 1<cutoff) (hr : 0<r) (k : ℤ) (reverse : Bool)
    (h0 : momentZero G S I z q cutoff≤E₀) (h2 : momentTwo G S I z q cutoff≤E₂) :
    |averagedDifference G S I z q cutoff r k reverse|≤
      Real.sqrt (E₀*((1-r)^2*E₀+r*E₂)) := by
  obtain ⟨hn0,hn2⟩:=moments_nonneg G S I (q:=q) hz (by linarith) hc
  apply (actual_averaged_error G S I hz hv hc hr k reverse).trans
  apply Real.sqrt_le_sqrt
  exact mul_le_mul h0
    (add_le_add (mul_le_mul_of_nonneg_left h0 (sq_nonneg _))
      (mul_le_mul_of_nonneg_left h2 hr.le)) (by positivity) (hn0.trans h0)


noncomputable def zeroBudget (alpha m v eta D : ℝ) : ℝ :=
  PointMassErrorEnvelope.costOne alpha m v eta*
    (1+NegativePowerHermite.coefficient 1 alpha*D/m)+
  PointMassErrorEnvelope.costThreeHalves alpha m v*
    (1+NegativePowerHermite.coefficient (3/2) alpha*D/m)+
  gaussianZero (v*(alpha*m))

noncomputable def twoBudget (alpha m v eta D : ℝ) : ℝ :=
  DirectionalErrorEnvelope.costTwo alpha m v eta*
    (1+NegativePowerHermite.coefficient 2 alpha*D/m)+
  DirectionalErrorEnvelope.costFiveHalves alpha m v*
    (1+NegativePowerHermite.coefficient (5/2) alpha*D/m)+
  gaussianTwo (v*(alpha*m))

theorem two_power_average (G : SimpleGraph V) (S I : Finset V)
    (hIS : I⊆S) (hI : G.IsIndepSet (I:Set V)) {z alpha m D p₁ p₂ C₁ C₂ T : ℝ}
    (hz : 0≤z) (hm : m=hardCoreAvailableMean G S I z) (hm0 : 0<m)
    (ha : 0<alpha) (ha1 : alpha<1) (hp₁ : 0<p₁) (hp₂ : 0<p₂)
    (hC₁ : 0≤C₁) (hC₂ : 0≤C₂) (hT : 0≤T)
    (hvar : hardCoreAvailableVariance G S I z≤D*m) (f : ℕ→ℝ)
    (hf : ∀(M:ℕ),alpha*m≤(M:ℝ)→f M≤C₁*((M:ℝ)/m)^(-p₁)+C₂*((M:ℝ)/m)^(-p₂)+T) :
    hardCoreLayerExpectation G S I z (fun _ M=>if alpha*m≤(M:ℝ) then f M else 0)≤
      C₁*(1+NegativePowerHermite.coefficient p₁ alpha*D/m)+
      C₂*(1+NegativePowerHermite.coefficient p₂ alpha*D/m)+T := by
  have h1:=single_hermite_layer_bound G S I hIS hI hz hm hm0 hp₁ ha ha1 hvar
  have h2:=single_hermite_layer_bound G S I hIS hI hz hm hm0 hp₂ ha ha1 hvar
  have h:=layer_mono G S I hz
    (fun _ M=>if alpha*m≤(M:ℝ) then f M else 0)
    (fun _ M=>C₁*(if alpha*m≤(M:ℝ) then ((M:ℝ)/m)^(-p₁) else 0)+
      C₂*(if alpha*m≤(M:ℝ) then ((M:ℝ)/m)^(-p₂) else 0)+T) (by
    intro j M
    by_cases hM : alpha*m≤(M:ℝ)
    · simpa only [if_pos hM] using hf M hM
    · simpa only [if_neg hM,mul_zero,zero_add] using hT)
  rw [layer_add,layer_add,layer_const_mul,layer_const_mul,
    layer_const G S I hIS hI hz] at h
  exact h.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left h1 hC₁)
    (mul_le_mul_of_nonneg_left h2 hC₂)) le_rfl)

theorem moments_le_explicit (G : SimpleGraph V) (S I : Finset V)
    (hIS : I⊆S) (hI : G.IsIndepSet (I:Set V)) {z alpha m v eta D : ℝ}
    (hz : 0≤z) (hm : m=hardCoreAvailableMean G S I z) (hm0 : 0<m)
    (ha : 0<alpha) (ha1 : alpha<1) (ham : 1<alpha*m)
    (hv : 0<v) (hvq : v≤(z/(1+z))*(1-z/(1+z)))
    (heta : |1-2*(z/(1+z))|≤eta)
    (hvar : hardCoreAvailableVariance G S I z≤D*m) :
    momentZero G S I z (z/(1+z)) (alpha*m)≤zeroBudget alpha m v eta D ∧
      momentTwo G S I z (z/(1+z)) (alpha*m)≤twoBudget alpha m v eta D := by
  have heta0:=(abs_nonneg (1-2*(z/(1+z)))).trans heta
  have hr:=PointMassErrorEnvelope.rho_pos ham
  constructor
  · apply two_power_average G S I hIS hI hz hm hm0 ha ha1
      (p₁:=1) (p₂:=3/2) (by norm_num) (by norm_num)
      (C₁:=PointMassErrorEnvelope.costOne alpha m v eta)
      (C₂:=PointMassErrorEnvelope.costThreeHalves alpha m v)
      (T:=gaussianZero (v*(alpha*m)))
      (PointMassErrorEnvelope.costOne_nonneg hm0.le hv.le heta0)
      (PointMassErrorEnvelope.costThreeHalves_nonneg hm0 ham hv)
      (by unfold gaussianZero;positivity) hvar
    intro M hM
    exact DirectionalErrorEnvelope.errorZero_le M hm0 ham hM hv hvq heta
  · apply two_power_average G S I hIS hI hz hm hm0 ha ha1
      (p₁:=2) (p₂:=5/2) (by norm_num) (by norm_num)
      (C₁:=DirectionalErrorEnvelope.costTwo alpha m v eta)
      (C₂:=DirectionalErrorEnvelope.costFiveHalves alpha m v)
      (T:=gaussianTwo (v*(alpha*m)))
      (by unfold DirectionalErrorEnvelope.costTwo;positivity)
      (by unfold DirectionalErrorEnvelope.costFiveHalves;positivity)
      (by unfold gaussianTwo;positivity) hvar
    intro M hM
    exact DirectionalErrorEnvelope.errorTwo_le M hm0 ham hM hv hvq heta

/-- Both Fourier moments and the comparison itself are now derived from the
actual graph layer distribution. Only mean and variance statistics remain. -/
theorem actual_averaged_error_explicit (G : SimpleGraph V) (S I : Finset V)
    (hIS : I⊆S) (hI : G.IsIndepSet (I:Set V)) {z alpha m v eta D r : ℝ}
    (hz : 0≤z) (hm : m=hardCoreAvailableMean G S I z) (hm0 : 0<m)
    (ha : 0<alpha) (ha1 : alpha<1) (ham : 1<alpha*m)
    (hv : 0<v) (hvq : v≤(z/(1+z))*(1-z/(1+z)))
    (hvnear : 9/40≤(z/(1+z))*(1-z/(1+z)))
    (heta : |1-2*(z/(1+z))|≤eta)
    (hvar : hardCoreAvailableVariance G S I z≤D*m)
    (hr : 0<r) (k : ℤ) (reverse : Bool) :
    |averagedDifference G S I z (z/(1+z)) (alpha*m) r k reverse|≤
      Real.sqrt (zeroBudget alpha m v eta D*
        ((1-r)^2*zeroBudget alpha m v eta D+r*twoBudget alpha m v eta D)) := by
  obtain ⟨h0,h2⟩:=moments_le_explicit G S I hIS hI hz hm hm0 ha ha1 ham hv hvq heta hvar
  exact actual_averaged_error_of_budgets G S I hz hvnear ham hr k reverse h0 h2

#print axioms actual_averaged_error
#print axioms actual_averaged_error_of_budgets
#print axioms moments_le_explicit
#print axioms actual_averaged_error_explicit
end ForestUnimodality.DirectionalErrorLayerBudget
