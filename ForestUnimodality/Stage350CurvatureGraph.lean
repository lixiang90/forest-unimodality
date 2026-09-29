import ForestUnimodality.Stage350CurvatureNormalization
import ForestUnimodality.SignedGaussianShiftedLayerBudget

namespace ForestUnimodality.Stage350CurvatureGraph
open Finset Set Real Stage350CurvatureBudget
open NegativePowerLayerBudget SignedGaussian350Profile
open ShiftedCurvatureErrorLayerBudget
open CurvatureErrorLayerBudget (scale)
variable {V : Type*} [DecidableEq V]

noncomputable def gapRateAt (p : Parameters) (i : ℕ) : ℝ := p.gapRate ⟨i%40,Nat.mod_lt _ (by decide)⟩
noncomputable def badRateAt (p : Parameters) (i : ℕ) : ℝ := p.badRate ⟨i%24,Nat.mod_lt _ (by decide)⟩

structure Inputs (p : Parameters) (G : SimpleGraph V) (S I : Finset V) (z m : ℝ) (k : ℕ) : Prop where
  subset : I⊆S
  independent : G.IsIndepSet (I:Set V)
  activity_pos : 0<z
  mean_eq : m=hardCoreAvailableMean G S I z
  start_le : p.start≤m
  rank_eq : hardCoreMean G S z=(k:ℝ)
  variance_center : hardCoreVariance G S z-(z/(1+z))*(1-z/(1+z))*m≤
    p.R*((z/(1+z))*(1-z/(1+z))*m)
  variance_available : hardCoreAvailableVariance G S I z≤p.D*m
  variance_min : p.vmin≤(z/(1+z))*(1-z/(1+z))
  variance_max : (z/(1+z))*(1-z/(1+z))≤p.vmax
  near : 9/40≤(z/(1+z))*(1-z/(1+z))
  asymmetry : |1-2*(z/(1+z))|≤p.eta
  gap_tails : ∀i : Fin 40,hardCoreAvailableLowerTail G S I z (profileCut p.largeBeta (i.val+1)*m)≤
    exp (-p.gapRate i*m)
  bad_tails : ∀i : Fin 24,hardCoreAvailableLowerTail G S I z (cut i.val*m)≤exp (-p.badRate i*m)

theorem profile_parameters (large : Bool) :
    (7/20:ℝ)<beta large ∧ beta large≤1 ∧
    -B large≤SignedGaussianHermite.coefficient parameter (beta large) := by
  cases large
  · exact ⟨by norm_num [beta,SignedGaussian350Data.Beta60.beta],
      by norm_num [beta,SignedGaussian350Data.Beta60.beta],SignedGaussian350Data.Beta60.curvature_lower⟩
  · exact ⟨by norm_num [beta,SignedGaussian350Data.Beta65.beta],
      by norm_num [beta,SignedGaussian350Data.Beta65.beta],SignedGaussian350Data.Beta65.curvature_lower⟩

theorem profile_cuts (large : Bool) : profileCut large 0=(7/20:ℝ) ∧
    profileCut large 40=beta large ∧ ∀i : ℕ,profileCut large i≤profileCut large (i+1) := by
  refine ⟨by norm_num [profileCut],by norm_num [profileCut],?_⟩
  intro i
  unfold profileCut
  push_cast
  nlinarith [(profile_parameters large).1]

theorem profile_prices (large : Bool) (i : ℕ) (hi : i≤39) :
    SignedGaussianHermite.positiveGap parameter (-B large) (profileCut large i)≤prices large i := by
  cases large
  · exact SignedGaussian350Data.Beta60.prices_upper i hi
  · exact SignedGaussian350Data.Beta65.prices_upper i hi

theorem bad_sign {p : Parameters} (hp : p.Valid)
    (hbad : let t:=((7/20:ℝ)*p.start+1/(6*p.vmin))/(p.start+1/(6*p.vmin))
      exp (-(9/20:ℝ))*(209/200+(159/200)*(t-1))-B p.largeBeta*(t-1)^2≤0)
    {m : ℝ} (hm : p.start≤m) :
    let t:=((7/20:ℝ)*m+1/(6*p.vmin))/(m+1/(6*p.vmin))
    SignedGaussianProfile.profile parameter 1+SignedGaussianProfile.first parameter 1*(t-1)+
      (-B p.largeBeta)*(t-1)^2≤0 := by
  have hs : 0<p.start := by linarith [hp.start_large]
  have hm0:=hs.trans_le hm
  have hv:=hp.vmin_pos
  let c : ℝ:=1/(6*p.vmin)
  have hc : 0≤c := by dsimp [c]; positivity
  have hT : ((7/20:ℝ)*m+c)/(m+c)≤((7/20:ℝ)*p.start+c)/(p.start+c) := by
    apply (div_le_div_iff₀ (by linarith : 0<m+c) (by linarith : 0<p.start+c)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) hc]
  have ht1 : ((7/20:ℝ)*p.start+c)/(p.start+c)≤1 := by
    apply (div_le_iff₀ (by linarith : 0<p.start+c)).mpr
    linarith
  have hh:=ShiftedLayerMoments.quadratic_nonpos_below (H:=SignedGaussianProfile.profile parameter 1)
    (show 0≤SignedGaussianProfile.first parameter 1 by rw [first_one]; positivity)
    (show 0≤parameter/2 by have := parameter_bounds.1; positivity) (B_pos p.largeBeta).le ht1 hT
    (by rw [profile_one,first_one]; dsimp only [c] at hbad ⊢; nlinarith) (w:=0)
  simpa only [ShiftedLayerMoments.quadratic,pow_two,mul_zero,sub_zero,neg_mul,sub_eq_add_neg,neg_zero,add_zero,c] using hh

theorem actual_main_lower {p : Parameters} (hp : p.Valid)
    {G : SimpleGraph V} {S I : Finset V} {z m : ℝ} {k : ℕ} (h : Inputs p G S I z m k)
    (hbad : let t:=((7/20:ℝ)*p.start+1/(6*p.vmin))/(p.start+1/(6*p.vmin))
      exp (-(9/20:ℝ))*(209/200+(159/200)*(t-1))-B p.largeBeta*(t-1)^2≤0) :
    main p m≤hardCoreLayerExpectation G S I z (fun j M=>if (7/20:ℝ)*m≤(M:ℝ) then
      SignedGaussianLayerBudget.kernel (ShiftedLayerMoments.ratio m (1/(6*((z/(1+z))*(1-z/(1+z))))) M)
        (ShiftedLayerMoments.offset z m (1/(6*((z/(1+z))*(1-z/(1+z))))) k
          ((z/(1+z))*(1-z/(1+z))) j M) else 0) := by
  have hm0 : 0<m := by linarith [hp.start_large,h.start_le]
  have hv:=hp.vmin_pos.trans_le h.variance_min
  have hb:=profile_parameters p.largeBeta
  have hc:=profile_cuts p.largeBeta
  have ht (i : ℕ) (hi : i≤39) :
      hardCoreAvailableLowerTail G S I z (profileCut p.largeBeta (i+1)*m)≤exp (-m*gapRateAt p i) := by
    have he (r : ℝ) : -r*m = -m*r := by ring
    simpa only [gapRateAt,Nat.mod_eq_of_lt (show i<40 by omega),he] using h.gap_tails ⟨i,by omega⟩
  have hh:=SignedGaussianShiftedLayerBudget.actual_normalized_lower G S I h.subset h.independent
    h.activity_pos h.mean_eq hm0 (by positivity : 0≤1/(6*((z/(1+z))*(1-z/(1+z)))))
    (show 1/(6*((z/(1+z))*(1-z/(1+z))))≤1/(6*p.vmin) by
      apply one_div_le_one_div_of_le (by have := hp.vmin_pos; positivity); gcongr; exact h.variance_min)
    h.rank_eq hv hp.R_nonneg hp.D_nonneg parameter_bounds.1 parameter_bounds.2
    (by norm_num : (0:ℝ)<7/20) hb.1 hb.2.1 hb.2.2 (neg_nonpos.mpr (B_pos p.largeBeta).le)
    (show 0≤SignedGaussianProfile.first parameter 1 by rw [first_one]; positivity)
    (bad_sign hp hbad h.start_le) h.variance_center h.variance_available
    (profileCut p.largeBeta) (prices p.largeBeta) (gapRateAt p) 39 hc.1 hc.2.1
    (fun i _=>hc.2.2 i) (profile_prices p.largeBeta)
    (fun i hi=>prices_step p.largeBeta i (by omega))
    (by cases p.largeBeta <;> rfl) ht
  rw [profile_one] at hh
  have hsum : (∑i∈range 40,(prices p.largeBeta i-prices p.largeBeta (i+1))*exp (-m*gapRateAt p i))=gapCost p m := by
    rw [←Fin.sum_univ_eq_sum_range]
    unfold gapCost
    apply sum_congr rfl
    intro i _
    simp only [gapRateAt,Nat.mod_eq_of_lt i.isLt]
    congr 2
    ring
  simp only [show 39+1=40 by decide] at hh
  rw [hsum] at hh
  unfold main
  unfold parameter at hh
  simp only [neg_mul,neg_div] at hh
  linarith

theorem normalized_bad_le (p : Parameters) {q m : ℝ}
    (hv : 0<q*(1-q)) (hm : 0<m) (hvp : q*(1-q)≤p.vmax) :
    scale (q*(1-q)) m*(exp (-badRateAt p 0*m)+
      badPrice q (cut 22*m)*exp (-badRateAt p 23*m)+
      ∑i∈range 22,(badPrice q (cut i*m)-badPrice q (cut (i+1)*m))*exp (-badRateAt p (i+1)*m))≤bad p m := by
  have hV:=hv.trans_le hvp
  have hscale : scale (q*(1-q)) m≤sqrt (2*Real.pi)*p.vmax*sqrt p.vmax*(m*sqrt m) := by
    unfold scale
    rw [sqrt_mul hv.le]
    have hh : q*(1-q)*sqrt (q*(1-q))≤p.vmax*sqrt p.vmax :=
      mul_le_mul hvp (sqrt_le_sqrt hvp) (sqrt_nonneg _) hV.le
    nlinarith [mul_le_mul_of_nonneg_left hh (show 0≤sqrt (2*Real.pi)*(m*sqrt m) by positivity)]
  have hsum : (∑i∈range 22,scale (q*(1-q)) m*
      ((badPrice q (cut i*m)-badPrice q (cut (i+1)*m))*exp (-badRateAt p (i+1)*m)))=
      ∑i : Fin 22,((cut i.val)^(-(3/2:ℝ))-(cut (i.val+1))^(-(3/2:ℝ)))*
        exp (-p.badRate ⟨i.val+1,by omega⟩*m) := by
    rw [←Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro i _
    rw [←mul_assoc,mul_sub,scale_badPrice hv hm (cut_pos _),scale_badPrice hv hm (cut_pos _)]
    simp only [badRateAt,Nat.mod_eq_of_lt (show i.val+1<24 by omega)]
  rw [mul_add,mul_add,Finset.mul_sum,hsum,←mul_assoc (scale _ _) (badPrice _ _),
    scale_badPrice hv hm (cut_pos 22)]
  unfold bad UnboundedBudget.powerExpCost
  rw [PointMassSqrtNormalization.rpow_three_halves hm]
  simp only [badRateAt,Nat.zero_mod,show 23%24=23 by decide]
  have hh:=mul_le_mul_of_nonneg_right hscale (exp_pos (-p.badRate 0*m)).le
  have hz : p.badRate ⟨0,by decide⟩=p.badRate 0 := congrArg p.badRate (Fin.ext (by rfl))
  have hl : p.badRate ⟨23,by decide⟩=p.badRate 23 := congrArg p.badRate (Fin.ext (by rfl))
  rw [hz,hl]
  simp only [mul_assoc] at hh ⊢
  linarith

theorem actual_lower {p : Parameters} (hp : p.Valid)
    (hmainStart : 0≤main p p.start)
    (hbad : let t:=((7/20:ℝ)*p.start+1/(6*p.vmin))/(p.start+1/(6*p.vmin))
      exp (-(9/20:ℝ))*(209/200+(159/200)*(t-1))-B p.largeBeta*(t-1)^2≤0)
    {G : SimpleGraph V} {S I : Finset V} {z m : ℝ} {k : ℕ}
    (h : Inputs p G S I z m k) (hk : 1≤k) :
    budget p m≤scale ((z/(1+z))*(1-z/(1+z))) m*
      tiltedCenter (countIndependent G S) z (partitionFunction G S z) k := by
  have hs : 0<p.start := by linarith [hp.start_large]
  have hm0:=hs.trans_le h.start_le
  have hm6 : 6≤m := hp.start_large.trans h.start_le
  have hv:=hp.vmin_pos.trans_le h.variance_min
  have hscale : 0<scale ((z/(1+z))*(1-z/(1+z))) m := by unfold scale; positivity
  have htail (i : ℕ) (hi : i≤23) : hardCoreAvailableLowerTail G S I z (cut i*m)≤exp (-badRateAt p i*m) := by
    simpa only [badRateAt,Nat.mod_eq_of_lt (show i<24 by omega)] using h.bad_tails ⟨i,by omega⟩
  have hsteps (i : ℕ) (_hi : i≤22) : cut i*m≤cut (i+1)*m :=
    mul_le_mul_of_nonneg_right (cut_step i) hm0.le
  have hraw:=curvature_lower_of_slices G S I h.subset h.independent h.activity_pos k hk
    (show 2≤(7/20:ℝ)*m by linarith) h.near (fun i=>cut i*m) 22
    (mul_pos (cut_pos 0) hm0) (by norm_num [cut]) hsteps
  have herr:=error_layer_bound G S I h.subset h.independent h.activity_pos.le h.mean_eq hm0
    (by norm_num : (0:ℝ)<7/20) (by norm_num : (7/20:ℝ)<1) (by linarith : 1<(7/20:ℝ)*m)
    hv le_rfl h.asymmetry h.variance_available
  have hbadLayer:=bad_cost_layer_cumulative G S I h.activity_pos.le hv
    (fun i=>cut i*m) (fun i=>exp (-badRateAt p i*m)) 22 (mul_pos (cut_pos 0) hm0) hsteps htail
  have hmul:=mul_le_mul_of_nonneg_left hraw hscale.le
  have herrmul:=mul_le_mul_of_nonneg_left herr hscale.le
  rw [scale_averagedError hv hm0] at herrmul
  have herrnorm:=normalizedError_le_central (by norm_num : (1/3:ℝ)≤7/20) hm0
    (by linarith : 1<(7/20:ℝ)*m) hp.vmin_pos h.variance_min h.variance_max hp.eta_nonneg hp.D_nonneg
  rw [centralError_eq p hm0] at herrnorm
  have hbadnorm:=(mul_le_mul_of_nonneg_left hbadLayer hscale.le).trans (normalized_bad_le p hv hm0 h.variance_max)
  have hmain0:=hmainStart.trans (main_monotone hp (le_refl _) h.start_le)
  have hmain:=actual_main_lower hp h hbad
  rw [SignedGaussianShiftedLayerBudget.retained_kernel_eq_lattice_curvature G S I hm0 hv
    (by norm_num : (0:ℝ)<7/20)] at hmain
  have hcc : 1/(6*((z/(1+z))*(1-z/(1+z))))≤1/(6*p.vmin) := by
    apply one_div_le_one_div_of_le (by have := hp.vmin_pos; positivity)
    gcongr
    exact h.variance_min
  have hshift (v : ℝ) (hv : 0<v) : v*(m+1/(6*v))=v*m+1/6 := by field_simp
  rw [←hshift _ hv] at hmain
  have hmain2:=SignedGaussianShiftedLayerBudget.original_scale_lower hm0
    (by positivity : 0≤1/(6*((z/(1+z))*(1-z/(1+z))))) hcc hv hmain0
    hmain
  have hfactor:=mul_le_mul_of_nonneg_right (shiftFactor_mono hs h.start_le
    (show 0≤1/(6*p.vmin) by have := hp.vmin_pos; positivity)) hmain0
  change shiftFactor m (1/(6*p.vmin))*main p m≤scale ((z/(1+z))*(1-z/(1+z))) m*_ at hmain2
  have hmainFinal:=hfactor.trans hmain2
  have hswap (j M : ℕ) :
      GaussianCurvatureFourier.curvature ((M:ℝ)*((z/(1+z))*(1-z/(1+z)))+1/6)
        ((k:ℝ)-binomialLayerMean j M z)=
      GaussianCurvatureFourier.curvature (((z/(1+z))*(1-z/(1+z)))*(M:ℝ)+1/6)
        ((k:ℝ)-binomialLayerMean j M z) := by rw [mul_comm (M:ℝ)]
  simp_rw [hswap] at hmul
  rw [mul_sub,mul_sub] at hmul
  change _≤scale ((z/(1+z))*(1-z/(1+z))) m*tiltedCenter (countIndependent G S) z (partitionFunction G S z) k at hmul
  unfold budget
  linarith

theorem actual_positive {p : Parameters} (hp : p.Valid)
    (hmainStart : 0≤main p p.start) (hbudget : 0<budget p p.start)
    (hbad : let t:=((7/20:ℝ)*p.start+1/(6*p.vmin))/(p.start+1/(6*p.vmin))
      exp (-(9/20:ℝ))*(209/200+(159/200)*(t-1))-B p.largeBeta*(t-1)^2≤0)
    {G : SimpleGraph V} {S I : Finset V} {z m : ℝ} {k : ℕ}
    (h : Inputs p G S I z m k) (hk : 1≤k) :
    0<tiltedCenter (countIndependent G S) z (partitionFunction G S z) k := by
  have hs : 0<p.start := by linarith [hp.start_large]
  have hv:=hp.vmin_pos.trans_le h.variance_min
  have hscale : 0<scale ((z/(1+z))*(1-z/(1+z))) m := by
    have hm:=hs.trans_le h.start_le
    unfold scale
    positivity
  have hh:=(budget_positive hp hbudget h.start_le).trans_le
    (actual_lower hp hmainStart hbad h hk)
  exact (mul_pos_iff_of_pos_left hscale).mp hh

#print axioms bad_sign
#print axioms actual_main_lower
#print axioms normalized_bad_le
#print axioms actual_lower
#print axioms actual_positive
end ForestUnimodality.Stage350CurvatureGraph
