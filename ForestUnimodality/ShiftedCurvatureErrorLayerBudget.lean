import ForestUnimodality.CurvatureErrorLayerBudget
import ForestUnimodality.PointMassBudgetMonotonicity
import ForestUnimodality.PointMassSqrtNormalization

/-! Stage-350 errors for the actual variance-matched Gaussian Mv+1/6.
The triangular cost has exponent 7/2 and coefficient 1/96. -/
namespace ForestUnimodality.ShiftedCurvatureErrorLayerBudget
open Real Set NegativePowerLayerBudget CurvatureErrorLayerBudget

noncomputable def error (M : ℕ) (q : ℝ) : ℝ :=
  let v:=q*(1-q)
  let rho:=(M:ℝ)/((M:ℝ)-1)
  4*|1-2*q| *rho^3/(3*Real.pi*((M:ℝ)*v)^2)+
    5*rho^(7/2:ℝ)/(16*sqrt (2*Real.pi)*((M:ℝ)*v)^(5/2:ℝ))+
    1/(96*sqrt (2*Real.pi)*((M:ℝ)*v)^(7/2:ℝ))+
    gaussianTail ((M:ℝ)*v)

theorem binomial_error (M : ℕ) (hM : 2≤M) (j : ℤ) {q : ℝ}
    (hv : 9/40≤q*(1-q)) :
    |curvature M j q-GaussianCurvatureFourier.curvature ((M:ℝ)*(q*(1-q))+1/6)
      ((j:ℝ)-M*q)|≤error M q := by
  have h:=BinomialCurvatureError.binomial_curvature_error_bound M hM j hv
  dsimp only at h
  unfold curvature error gaussianTail
  convert! h using 1
  ring

open BinomialCurvatureError in
/-- Near symmetry controls the whole period, including every positive
integer free count. This is the sharp Gaussian price for the bad layers. -/
theorem abs_curvature_le (M : ℕ) (hM : 0<M) (j : ℤ) {q : ℝ}
    (hv : 9/40≤q*(1-q)) :
    |curvature M j q|≤1/(sqrt (2*Real.pi)*((M:ℝ)*(q*(1-q)))*sqrt ((M:ℝ)*(q*(1-q)))) := by
  have hm : 0<(M:ℝ) := by exact_mod_cast hM
  have hv0 : 0<q*(1-q) := by linarith
  have ha : 0<(M:ℝ)*(q*(1-q)) := mul_pos hm hv0
  have hb:=norm_periodIntegral_le_even ha (by norm_num : (0:ℝ)≤1) 1
    (f:=actualCurvatureIntegrand M q ((j:ℝ)-M*q))
    (by unfold actualCurvatureIntegrand BinomialCurvatureError.oscillation centeredBernoulliCharacteristic TriangularGaussian.kernel; fun_prop) ?_
  · rw [show 2*1=2 by decide,GaussianKernelMoments.integral_second_fourier ha,one_mul,
      ←binomial_curvature_eq_periodIntegral,Complex.norm_real,Real.norm_eq_abs] at hb
    exact hb
  · intro t ht
    rw [actualCurvatureIntegrand,norm_mul,norm_mul,norm_oscillation,one_mul,
      Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg t) (TriangularGaussian.kernel_nonneg t))]
    have hk : t^2*TriangularGaussian.kernel t≤t^2 := by
      nlinarith [sq_nonneg t,TriangularGaussian.kernel_le_one t]
    have he:=centeredBernoulliCharacteristic_pow_norm_le_gaussian M hv (abs_le.mpr ht)
    calc
      _≤t^2*exp (-(M:ℝ)*(q*(1-q))*t^2/2) := mul_le_mul hk he (norm_nonneg _) (sq_nonneg t)
      _=_ := by
        simp only [one_mul,show 2*1=2 by decide]
        congr 2
        ring

noncomputable def badPrice (q x : ℝ) : ℝ :=
  1/(sqrt (2*Real.pi)*(x*(q*(1-q)))*sqrt (x*(q*(1-q))))

noncomputable def badCost (q : ℝ) (cuts : ℕ→ℝ) (n : ℕ) (M : ℕ) : ℝ :=
  (if (M:ℝ)<cuts 0 then 1 else 0)+
    ∑i∈Finset.range (n+1),badPrice q (cuts i)*
      (if cuts i≤(M:ℝ) ∧ (M:ℝ)<cuts (i+1) then 1 else 0)

theorem badPrice_nonneg {q x : ℝ} (hv : 0<q*(1-q)) (hx : 0<x) : 0≤badPrice q x := by
  unfold badPrice
  positivity

theorem badPrice_antitone {q x y : ℝ} (hv : 0<q*(1-q)) (hx : 0<x) (hxy : x≤y) :
    badPrice q y≤badPrice q x := by
  have hy:=hx.trans_le hxy
  unfold badPrice
  apply one_div_le_one_div_of_le (by positivity)
  gcongr

variable {V : Type*} [DecidableEq V]

theorem curvature_lower_of_slices (G : SimpleGraph V) (S I : Finset V)
    (hIS : I⊆S) (hI : G.IsIndepSet (I:Set V)) {z cutoff : ℝ} (hz : 0<z)
    (k : ℕ) (hk : 1≤k) (hcut : 2≤cutoff)
    (hv : 9/40≤(z/(1+z))*(1-z/(1+z)))
    (cuts : ℕ→ℝ) (n : ℕ) (hstart : 0<cuts 0) (hend : cuts (n+1)=cutoff)
    (hsteps : ∀i ≤ n,cuts i ≤ cuts (i+1)) :
    hardCoreLayerExpectation G S I z (fun j M=>if cutoff≤(M:ℝ) then
      GaussianCurvatureFourier.curvature ((M:ℝ)*((z/(1+z))*(1-z/(1+z)))+1/6)
        ((k:ℝ)-binomialLayerMean j M z) else 0)-
    hardCoreLayerExpectation G S I z (fun _ M=>if cutoff≤(M:ℝ) then error M (z/(1+z)) else 0)-
    hardCoreLayerExpectation G S I z (fun _ M=>badCost (z/(1+z)) cuts n M) ≤
    2*tiltedProbability (countIndependent G S) z (partitionFunction G S z) k-
      tiltedProbability (countIndependent G S) z (partitionFunction G S z) (k-1)-
      tiltedProbability (countIndependent G S) z (partitionFunction G S z) (k+1) := by
  rw [actual_curvature_eq_layer G S I hIS hI hz k hk,←layer_sub,←layer_sub]
  apply layer_mono G S I hz.le
  intro j M
  let q:=z/(1+z)
  have hq0 : 0≤q := by dsimp [q]; positivity
  have hq1 : q≤1 := by dsimp [q]; exact (div_le_one (by positivity)).mpr (by linarith)
  have hv0 : 0<q*(1-q) := by dsimp [q]; linarith
  have hci (i : ℕ) (hi : i ≤ n+1) : 0 < cuts i := hstart.trans_le
    (NegativePowerLayerBudget.cut_le_of_steps cuts n hsteps (Nat.zero_le i) hi)
  have hterm (i : ℕ) (hi : i∈Finset.range (n+1)) : 0≤
      (1/(Real.sqrt (2*Real.pi)*(cuts i*(q*(1-q)))*
      Real.sqrt (cuts i*(q*(1-q))))) *
      (if cuts i ≤ (M:ℝ) ∧ (M:ℝ)<cuts (i+1) then 1 else 0) := by
    have hcp := hci i (by simp only [Finset.mem_range] at hi; omega)
    split_ifs <;> positivity
  have hsum := Finset.sum_nonneg hterm
  have hbad0 : 0≤badCost q cuts n M := by
    dsimp [badCost,badPrice,badPrice]
    split_ifs <;> linarith
  by_cases hgood : cutoff≤(M:ℝ)
  · have hM : 2≤M := by exact_mod_cast (hcut.trans hgood)
    have hb := (abs_le.mp (binomial_error M hM ((k:ℤ)-j) hv)).1
    have he : (((k:ℤ)-(j:ℤ):ℤ):ℝ)-M*q=(k:ℝ)-binomialLayerMean j M z := by
      push_cast
      dsimp [binomialLayerMean,q]
      ring
    rw [he] at hb
    simp only [if_pos hgood]
    change _-_-badCost q cuts n M≤_
    linarith
  · simp only [if_neg hgood,sub_self,zero_sub]
    change -badCost q cuts n M≤curvature M ((k:ℤ)-j) q
    by_cases hbottom : (M:ℝ)<cuts 0
    · have hb : 1≤badCost q cuts n M := by simpa only [badCost,badPrice,if_pos hbottom] using (le_add_of_nonneg_right hsum : (1:ℝ)≤1+_)
      linarith [curvature_ge_neg_one M ((k:ℤ)-j) hq0 hq1]
    · obtain ⟨i,hi,hilo,hihi⟩ := NegativePowerLayerBudget.exists_cut_interval cuts n
        (le_of_not_gt hbottom) (hend ▸ lt_of_not_ge hgood)
      have hcp:=hci i (by omega)
      have hMp : 0<(M:ℝ) := hcp.trans_le hilo
      have hMN : 0<M := by exact_mod_cast hMp
      have hab := (abs_le.mp (abs_curvature_le M hMN ((k:ℤ)-j) hv)).1
      have hden : cuts i*(q*(1-q))≤(M:ℝ)*(q*(1-q)) := mul_le_mul_of_nonneg_right hilo hv0.le
      have hprice : 1/(Real.sqrt (2*Real.pi)*((M:ℝ)*(q*(1-q)))*Real.sqrt ((M:ℝ)*(q*(1-q))))≤
          1/(Real.sqrt (2*Real.pi)*(cuts i*(q*(1-q)))*Real.sqrt (cuts i*(q*(1-q)))) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        gcongr
      have hsingle := Finset.single_le_sum hterm (Finset.mem_range.mpr (by omega : i<n+1))
      simp only [if_pos (And.intro hilo hihi),mul_one] at hsingle
      have hb : 1/(Real.sqrt (2*Real.pi)*(cuts i*(q*(1-q)))*Real.sqrt (cuts i*(q*(1-q))))≤badCost q cuts n M := by
        simpa only [badCost,badPrice,if_neg hbottom,zero_add] using hsingle
      linarith


noncomputable def costFiveHalves (alpha m v : ℝ) : ℝ :=
  ((5/16)*PointMassErrorEnvelope.rho alpha m^(7/2:ℝ)/sqrt (2*Real.pi))/(v*m)^(5/2:ℝ)

noncomputable def costSevenHalves (m v : ℝ) : ℝ :=
  (1/(96*sqrt (2*Real.pi)))/(v*m)^(7/2:ℝ)

noncomputable def averagedError (alpha m v eta D : ℝ) : ℝ :=
  costTwo alpha m v eta*(1+NegativePowerHermite.coefficient 2 alpha*D/m)+
  costFiveHalves alpha m v*(1+NegativePowerHermite.coefficient (5/2) alpha*D/m)+
  costSevenHalves m v*(1+NegativePowerHermite.coefficient (7/2) alpha*D/m)+
  gaussianTail (v*(alpha*m))

theorem error_le_power_envelope (M : ℕ) {q alpha m vminus eta : ℝ}
    (hm : 0<m) (ham : 1<alpha*m) (hM : alpha*m≤(M:ℝ))
    (hvm : 0<vminus) (hv : vminus≤q*(1-q)) (heta : |1-2*q|≤eta) :
    error M q≤costTwo alpha m vminus eta*((M:ℝ)/m)^(-2:ℝ)+
      costFiveHalves alpha m vminus*((M:ℝ)/m)^(-(5/2:ℝ))+
      costSevenHalves m vminus*((M:ℝ)/m)^(-(7/2:ℝ))+
      gaussianTail (vminus*(alpha*m)) := by
  have hM0 : 0<(M:ℝ) := by linarith
  have hv0 := hvm.trans_le hv
  have hr := PointMassErrorEnvelope.rho_pos ham
  have hMsub : 0<(M:ℝ)-1 := by linarith
  have hR : 0≤(M:ℝ)/((M:ℝ)-1) := by positivity
  have hRle : (M:ℝ)/((M:ℝ)-1)≤PointMassErrorEnvelope.rho alpha m :=
    PointMassErrorEnvelope.rho_antitone ham hM
  have heta0 := (abs_nonneg (1-2*q)).trans heta
  have hcost2 : costTwo alpha m vminus eta*((M:ℝ)/m)^(-2:ℝ)=
      (4*eta*PointMassErrorEnvelope.rho alpha m^3/(3*Real.pi))/((M:ℝ)*vminus)^2 := by
    unfold costTwo
    rw [←Real.rpow_two (vminus*m),PointMassErrorEnvelope.scaled_power_cost hM0 hm hvm,
      Real.rpow_two]
  have hcost52 : costFiveHalves alpha m vminus*((M:ℝ)/m)^(-(5/2:ℝ))=
      ((5/16)*PointMassErrorEnvelope.rho alpha m^(7/2:ℝ)/sqrt (2*Real.pi))/
        ((M:ℝ)*vminus)^(5/2:ℝ) := by
    unfold costFiveHalves
    rw [PointMassErrorEnvelope.scaled_power_cost hM0 hm hvm]
  have hcost72 : costSevenHalves m vminus*((M:ℝ)/m)^(-(7/2:ℝ))=
      (1/(96*sqrt (2*Real.pi)))/((M:ℝ)*vminus)^(7/2:ℝ) := by
    unfold costSevenHalves
    rw [PointMassErrorEnvelope.scaled_power_cost hM0 hm hvm]
  rw [hcost2,hcost52,hcost72]
  have hfirst : 4*|1-2*q| *((M:ℝ)/((M:ℝ)-1))^3/(3*Real.pi*((M:ℝ)*(q*(1-q)))^2)≤
      (4*eta*PointMassErrorEnvelope.rho alpha m^3/(3*Real.pi))/((M:ℝ)*vminus)^2 := by
    rw [div_div]
    apply div_le_div₀ (by positivity) ?_ (by positivity) ?_ <;> gcongr
  have hsecond : 5*((M:ℝ)/((M:ℝ)-1))^(7/2:ℝ)/
      (16*sqrt (2*Real.pi)*((M:ℝ)*(q*(1-q)))^(5/2:ℝ))≤
      ((5/16)*PointMassErrorEnvelope.rho alpha m^(7/2:ℝ)/sqrt (2*Real.pi))/
        ((M:ℝ)*vminus)^(5/2:ℝ) := by
    have he : ((5/16)*PointMassErrorEnvelope.rho alpha m^(7/2:ℝ)/sqrt (2*Real.pi))/
        ((M:ℝ)*vminus)^(5/2:ℝ)=
        5*PointMassErrorEnvelope.rho alpha m^(7/2:ℝ)/
          (16*sqrt (2*Real.pi)*((M:ℝ)*vminus)^(5/2:ℝ)) := by ring
    rw [he]
    apply div_le_div₀ (by positivity) ?_ (by positivity) ?_ <;> gcongr
  have hthird : 1/(96*sqrt (2*Real.pi)*((M:ℝ)*(q*(1-q)))^(7/2:ℝ))≤
      (1/(96*sqrt (2*Real.pi)))/((M:ℝ)*vminus)^(7/2:ℝ) := by
    rw [div_div]
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
  have htail := gaussianTail_antitone (show 0<vminus*(alpha*m) by positivity)
    (show vminus*(alpha*m)≤(M:ℝ)*(q*(1-q)) by nlinarith [mul_le_mul hM hv hvm.le hM0.le])
  exact add_le_add (add_le_add (add_le_add hfirst hsecond) hthird) htail

/-- All three inverse moments are taken under the same actual law and
bounded by the already proved Hermite inequality. -/
theorem error_layer_bound (G : SimpleGraph V) (S I : Finset V)
    (hIS : I⊆S) (hI : G.IsIndepSet (I:Set V)) {z alpha m vminus eta D : ℝ}
    (hz : 0≤z) (hm : m=hardCoreAvailableMean G S I z) (hm0 : 0<m)
    (ha : 0<alpha) (ha1 : alpha<1) (ham : 1<alpha*m)
    (hvm : 0<vminus) (hv : vminus≤(z/(1+z))*(1-z/(1+z)))
    (heta : |1-2*(z/(1+z))|≤eta)
    (hvar : hardCoreAvailableVariance G S I z≤D*m) :
    hardCoreLayerExpectation G S I z
      (fun _ M=>if alpha*m≤(M:ℝ) then error M (z/(1+z)) else 0)≤
      averagedError alpha m vminus eta D := by
  have heta0 := (abs_nonneg (1-2*(z/(1+z)))).trans heta
  have hr := PointMassErrorEnvelope.rho_pos ham
  have hc2 : 0≤costTwo alpha m vminus eta := by unfold costTwo; positivity
  have hc52 : 0≤costFiveHalves alpha m vminus := by unfold costFiveHalves; positivity
  have hc72 : 0≤costSevenHalves m vminus := by unfold costSevenHalves; positivity
  have htail := gaussianTail_nonneg (show 0<vminus*(alpha*m) by positivity)
  have hp := layer_mono G S I hz
    (fun _ M=>if alpha*m≤(M:ℝ) then error M (z/(1+z)) else 0)
    (fun _ M=>costTwo alpha m vminus eta*(if alpha*m≤(M:ℝ) then ((M:ℝ)/m)^(-2:ℝ) else 0)+
      costFiveHalves alpha m vminus*(if alpha*m≤(M:ℝ) then ((M:ℝ)/m)^(-(5/2:ℝ)) else 0)+
      costSevenHalves m vminus*(if alpha*m≤(M:ℝ) then ((M:ℝ)/m)^(-(7/2:ℝ)) else 0)+
      gaussianTail (vminus*(alpha*m))) (by
        intro j M
        by_cases hgood : alpha*m≤(M:ℝ)
        · simpa only [if_pos hgood] using error_le_power_envelope M hm0 ham hgood hvm hv heta
        · simpa only [if_neg hgood,mul_zero,zero_add] using htail)
  rw [layer_add,layer_add,layer_add,layer_const_mul,layer_const_mul,layer_const_mul,
    layer_const G S I hIS hI hz] at hp
  have h2:=single_hermite_layer_bound G S I hIS hI hz hm hm0 (by norm_num : (0:ℝ)<2) ha ha1 hvar
  have h52:=single_hermite_layer_bound G S I hIS hI hz hm hm0 (by norm_num : (0:ℝ)<5/2) ha ha1 hvar
  have h72:=single_hermite_layer_bound G S I hIS hI hz hm hm0 (by norm_num : (0:ℝ)<7/2) ha ha1 hvar
  exact hp.trans (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left h2 hc2)
    (mul_le_mul_of_nonneg_left h52 hc52)) (mul_le_mul_of_nonneg_left h72 hc72)) le_rfl)

theorem bad_cost_layer_eq (G : SimpleGraph V) (S I : Finset V) (z : ℝ)
    (cuts : ℕ→ℝ) (n : ℕ) :
    hardCoreLayerExpectation G S I z (fun _ M=>badCost (z/(1+z)) cuts n M)=
      hardCoreAvailableLowerTail G S I z (cuts 0)+
      ∑i∈Finset.range (n+1),badPrice (z/(1+z)) (cuts i)*
        hardCoreAvailableSlice G S I z (cuts i) (cuts (i+1)) := by
  unfold badCost
  rw [layer_add,layer_sum]
  simp only [layer_const_mul,hardCoreAvailableLowerTail,hardCoreAvailableSlice]

theorem bad_cost_layer_cumulative (G : SimpleGraph V) (S I : Finset V) {z : ℝ}
    (hz : 0≤z) (hv : 0<(z/(1+z))*(1-z/(1+z)))
    (cuts bound : ℕ→ℝ) (n : ℕ) (hstart : 0<cuts 0)
    (hsteps : ∀i≤n,cuts i≤cuts (i+1))
    (hbound : ∀i≤n+1,hardCoreAvailableLowerTail G S I z (cuts i)≤bound i) :
    hardCoreLayerExpectation G S I z (fun _ M=>badCost (z/(1+z)) cuts n M)≤
      bound 0+badPrice (z/(1+z)) (cuts n)*bound (n+1)+
      ∑i∈Finset.range n,(badPrice (z/(1+z)) (cuts i)-badPrice (z/(1+z)) (cuts (i+1)))*bound (i+1) := by
  rw [bad_cost_layer_eq]
  have hci (i : ℕ) (hi : i≤n+1) : 0<cuts i := hstart.trans_le
    (cut_le_of_steps cuts n hsteps (Nat.zero_le i) hi)
  have hb:=hardCoreAvailableSlices_le_cumulative G S I hz cuts (fun i=>badPrice (z/(1+z)) (cuts i)) bound n
    hsteps (badPrice_nonneg hv hstart) (badPrice_nonneg hv (hci n (by omega)))
    (fun i hi=>badPrice_antitone hv (hci i (by omega)) (hsteps i (by omega)))
    (fun i hi=>hbound (i+1) (by omega))
  have h0:=hbound 0 (by omega)
  linarith

theorem scale_badPrice {q m alpha : ℝ} (hv : 0<q*(1-q)) (hm : 0<m) (ha : 0<alpha) :
    scale (q*(1-q)) m*badPrice q (alpha*m)=alpha^(-(3/2:ℝ)) := by
  have hs : sqrt ((q*(1-q))*m)≠0 := (sqrt_pos.mpr (mul_pos hv hm)).ne'
  have haS : sqrt alpha≠0 := (sqrt_pos.mpr ha).ne'
  have hp : sqrt (2*Real.pi)≠0 := (sqrt_pos.mpr (by positivity)).ne'
  have he : alpha*m*(q*(1-q))=alpha*((q*(1-q))*m) := by ring
  unfold scale badPrice
  rw [he,sqrt_mul ha.le,PointMassSqrtNormalization.rpow_neg_three_halves ha]
  field_simp [hv.ne']
  exact div_self hv.ne'

noncomputable def normalizedError (alpha m v eta D : ℝ) : ℝ :=
  (4*sqrt (2*Real.pi)/(3*Real.pi))*eta*PointMassErrorEnvelope.rho alpha m^3*
      (1+NegativePowerHermite.coefficient 2 alpha*D/m)/sqrt (v*m)+
  (5/16)*PointMassErrorEnvelope.rho alpha m^(7/2:ℝ)*
      (1+NegativePowerHermite.coefficient (5/2) alpha*D/m)/(v*m)+
  (1+NegativePowerHermite.coefficient (7/2) alpha*D/m)/(96*(v*m)^2)+
  scale v m*gaussianTail (v*(alpha*m))

noncomputable def centralError (alpha m vminus vplus eta D : ℝ) : ℝ :=
  (4*sqrt (2*Real.pi)/(3*Real.pi))*eta*PointMassErrorEnvelope.rho alpha m^3*
      (1+NegativePowerHermite.coefficient 2 alpha*D/m)/sqrt (vminus*m)+
  (5/16)*PointMassErrorEnvelope.rho alpha m^(7/2:ℝ)*
      (1+NegativePowerHermite.coefficient (5/2) alpha*D/m)/(vminus*m)+
  (1+NegativePowerHermite.coefficient (7/2) alpha*D/m)/(96*(vminus*m)^2)+
  centralTail m vminus vplus

theorem scale_averagedError {v m : ℝ} (hv : 0<v) (hm : 0<m) (alpha eta D : ℝ) :
    scale v m*averagedError alpha m v eta D=normalizedError alpha m v eta D := by
  have hvm:=mul_pos hv hm
  have hs : sqrt (v*m)≠0 := (sqrt_pos.mpr hvm).ne'
  have hpi : sqrt (2*Real.pi)≠0 := (sqrt_pos.mpr (by positivity)).ne'
  have hsq : sqrt (v*m)^2=v*m := sq_sqrt hvm.le
  have hp5 : (v*m)^(5/2:ℝ)=(v*m)^2*sqrt (v*m) := by
    rw [show (5/2:ℝ)=(2:ℕ)+(1/2:ℝ) by norm_num,rpow_add hvm,rpow_natCast,←sqrt_eq_rpow]
  have hp7 : (v*m)^(7/2:ℝ)=(v*m)^3*sqrt (v*m) := by
    rw [show (7/2:ℝ)=(3:ℕ)+(1/2:ℝ) by norm_num,rpow_add hvm,rpow_natCast,←sqrt_eq_rpow]
  unfold averagedError normalizedError costTwo costFiveHalves costSevenHalves scale
  rw [hp5,hp7]
  field_simp [hv.ne',hm.ne',hs,hpi]
  ring_nf
  rw [hsq]
  ring

/-- The common full-period tail permits alpha at least 1/3. All power
costs retain their actual alpha; only the negligible tail is enlarged. -/
theorem normalizedError_le_central {alpha m vminus v vplus eta D : ℝ}
    (ha : (1/3:ℝ)≤alpha) (hm : 0<m) (ham : 1<alpha*m)
    (hvm : 0<vminus) (hvv : vminus≤v) (hvp : v≤vplus) (heta : 0≤eta) (hD : 0≤D) :
    normalizedError alpha m v eta D≤centralError alpha m vminus vplus eta D := by
  have ha0 : 0<alpha := by linarith
  have hv:=hvm.trans_le hvv
  have hvplus:=hv.trans_le hvp
  have hr:=PointMassErrorEnvelope.rho_pos ham
  have hc2:=PointMassBudgetMonotonicity.coefficient_nonneg (by norm_num : (0:ℝ)≤2) ha0
  have hc52:=PointMassBudgetMonotonicity.coefficient_nonneg (by norm_num : (0:ℝ)≤5/2) ha0
  have hc72:=PointMassBudgetMonotonicity.coefficient_nonneg (by norm_num : (0:ℝ)≤7/2) ha0
  have hfirst :
      (4*sqrt (2*Real.pi)/(3*Real.pi))*eta*PointMassErrorEnvelope.rho alpha m^3*
        (1+NegativePowerHermite.coefficient 2 alpha*D/m)/sqrt (v*m)≤
      (4*sqrt (2*Real.pi)/(3*Real.pi))*eta*PointMassErrorEnvelope.rho alpha m^3*
        (1+NegativePowerHermite.coefficient 2 alpha*D/m)/sqrt (vminus*m) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    gcongr
  have hsecond :
      (5/16)*PointMassErrorEnvelope.rho alpha m^(7/2:ℝ)*
        (1+NegativePowerHermite.coefficient (5/2) alpha*D/m)/(v*m)≤
      (5/16)*PointMassErrorEnvelope.rho alpha m^(7/2:ℝ)*
        (1+NegativePowerHermite.coefficient (5/2) alpha*D/m)/(vminus*m) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    gcongr
  have hthird : (1+NegativePowerHermite.coefficient (7/2) alpha*D/m)/(96*(v*m)^2)≤
      (1+NegativePowerHermite.coefficient (7/2) alpha*D/m)/(96*(vminus*m)^2) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    gcongr
  have hgauss : gaussianTail (v*(alpha*m))≤gaussianTail (vminus*((1/3)*m)) := by
    apply gaussianTail_antitone (by positivity)
    gcongr
  have hscale : scale v m≤scale vplus m := by unfold scale; gcongr
  have htail := (mul_le_mul hscale hgauss (gaussianTail_nonneg (by positivity))
    (show 0≤scale vplus m by unfold scale; positivity)).trans
      (scale_gaussianTail_le_central hm hvm hvplus)
  exact add_le_add (add_le_add (add_le_add hfirst hsecond) hthird) htail

#print axioms binomial_error
#print axioms abs_curvature_le
#print axioms curvature_lower_of_slices
#print axioms bad_cost_layer_cumulative
#print axioms scale_badPrice
#print axioms error_le_power_envelope
#print axioms error_layer_bound
#print axioms scale_averagedError
#print axioms normalizedError_le_central
end ForestUnimodality.ShiftedCurvatureErrorLayerBudget
