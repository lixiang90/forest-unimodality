import ForestUnimodality.BinomialCurvatureError
import ForestUnimodality.NegativePowerLayerBudget
import ForestUnimodality.ReciprocalGradientBudget
import ForestUnimodality.PointMassErrorEnvelope

/-! Curvature errors under the actual hard-core layer law. The Gaussian
variance here is M*q*(1-q), without the triangular variance shift 1/6. -/
namespace ForestUnimodality.CurvatureErrorLayerBudget
open Real Set MeasureTheory
open BinomialCurvatureError NegativePowerLayerBudget

noncomputable def curvature (M : ℕ) (j : ℤ) (q : ℝ) : ℝ :=
  2*binomialMass M j q-binomialMass M (j-1) q-binomialMass M (j+1) q

/-- A reusable even-moment bound, normalized as an actual Fourier coefficient. -/
theorem norm_periodIntegral_le_even {a c : ℝ} (ha : 0<a) (hc : 0≤c)
    (n : ℕ) {f : ℝ→ℂ} (hf : Continuous f)
    (hbound : ∀t∈Icc (-Real.pi) Real.pi,
      ‖f t‖≤c*(t^(2*n)*Real.exp (-a*t^2/2))) :
    ‖periodIntegral f‖≤c*((2*Real.pi)⁻¹*∫t:ℝ,t^(2*n)*Real.exp (-a*t^2/2)) := by
  let g : ℝ→ℝ := fun t=>c*(t^(2*n)*Real.exp (-a*t^2/2))
  have hg : Integrable g := (GaussianCurvatureTail.integrable_real_moment ha (2*n)).const_mul c
  have hgc : Continuous g := by dsimp [g]; fun_prop
  have hg0 (t : ℝ) : 0≤g t := by
    dsimp [g]
    exact mul_nonneg hc (mul_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg t) n) (Real.exp_pos _).le)
  have hord : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hfinite : (∫t in -Real.pi..Real.pi, ‖f t‖) ≤ ∫t in -Real.pi..Real.pi,g t := intervalIntegral.integral_mono_on hord (hf.norm.intervalIntegrable _ _)
    (hgc.intervalIntegrable _ _) hbound
  have hfull : (∫t in -Real.pi..Real.pi,g t)≤∫t:ℝ,g t := by
    rw [intervalIntegral.integral_of_le hord]
    exact setIntegral_le_integral hg (Filter.Eventually.of_forall hg0)
  have hn : ‖(2*(Real.pi:ℂ))⁻¹‖=(2*Real.pi)⁻¹ := by
    simp [norm_inv,Complex.norm_real,abs_of_pos Real.pi_pos]
  calc
    ‖periodIntegral f‖≤(2*Real.pi)⁻¹*∫t:ℝ,g t := by
      rw [periodIntegral,norm_mul,hn]
      exact mul_le_mul_of_nonneg_left
        ((intervalIntegral.norm_integral_le_integral_norm hord).trans (hfinite.trans hfull)) (by positivity)
    _ = _ := by dsimp [g]; rw [integral_const_mul]; ring

/-- The ordinary lattice loss, rather than the variance-shifted loss. -/
theorem lattice_loss_bounds (t : ℝ) :
    0≤t^2-t^2*TriangularGaussian.kernel t ∧
      t^2-t^2*TriangularGaussian.kernel t≤t^4/12 := by
  have hlo := TriangularGaussian.kernel_le_one t
  have hs := sinc_add_sq_monotone (show (0:ℝ)∈Ici 0 by simp)
    (show |t|/2∈Ici 0 by change 0≤|t|/2; positivity) (by positivity : (0:ℝ)≤|t|/2)
  simp only [Real.sinc_zero,zero_pow (by decide : 2≠0),zero_div,add_zero] at hs
  have he : Real.sinc (|t|/2)=Real.sinc (t/2) := by
    rcases le_or_gt 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg ht,neg_div,Real.sinc_neg]
  rw [he] at hs
  have ha : (|t|/2)^2=t^2/4 := by rw [div_pow,sq_abs]; norm_num
  rw [ha] at hs
  have hsq := sq_nonneg (Real.sinc (t/2)-1)
  constructor
  · nlinarith [sq_nonneg t]
  · have hh : 1-TriangularGaussian.kernel t≤t^2/12 := by
      dsimp [TriangularGaussian.kernel]
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hh (sq_nonneg t)]

theorem triangular_unshifted_period_bound {a : ℝ} (ha : 0<a) (d : ℝ) :
    ‖periodIntegral (latticeGaussianIntegrand a d)-
      periodIntegral (gaussianCurvatureIntegrand a d)‖≤
      1/(4*Real.sqrt (2*Real.pi)*a^2*Real.sqrt a) := by
  rw [norm_sub_rev,←periodIntegral_sub _ _
    (by unfold gaussianCurvatureIntegrand GaussianCurvatureFourier.phase; fun_prop)
    (by unfold latticeGaussianIntegrand BinomialCurvatureError.oscillation TriangularGaussian.kernel; fun_prop)]
  have he : (fun t=>gaussianCurvatureIntegrand a d t-latticeGaussianIntegrand a d t)=
      (fun t=>BinomialCurvatureError.oscillation d t*((t^2-t^2*TriangularGaussian.kernel t)*Real.exp (-a*t^2/2):ℝ)) := by
    funext t
    unfold gaussianCurvatureIntegrand latticeGaussianIntegrand BinomialCurvatureError.oscillation
    rw [GaussianCurvatureFourier.phase_eq]
    push_cast
    ring
  rw [he]
  have hb := norm_periodIntegral_le_even ha (by norm_num : (0:ℝ)≤1/12) 2
    (f:=fun t=>BinomialCurvatureError.oscillation d t*((t^2-t^2*TriangularGaussian.kernel t)*Real.exp (-a*t^2/2):ℝ))
    (by unfold BinomialCurvatureError.oscillation TriangularGaussian.kernel; fun_prop) ?_
  · rw [show 2*2=4 by decide,GaussianKernelMoments.integral_fourth_fourier ha] at hb
    convert hb using 1
    ring
  · intro t ht
    have hl := lattice_loss_bounds t
    rw [norm_mul,norm_oscillation,one_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hl.1 (Real.exp_pos _).le)]
    have hh := mul_le_mul_of_nonneg_right hl.2 (Real.exp_pos (-a*t^2/2)).le
    calc
      _ ≤ t^4/12*Real.exp (-a*t^2/2) := hh
      _ = _ := by ring

theorem gaussian_unshifted_period_bound {a : ℝ} (ha : 0<a) (d : ℝ) :
    ‖periodIntegral (gaussianCurvatureIntegrand a d)-
      (GaussianCurvatureFourier.curvature a d:ℂ)‖≤
      (1/a+1/(Real.pi^2*a^2))*Real.exp (-a*Real.pi^2/2) := by
  rw [norm_sub_rev,←GaussianCurvatureFourier.integral_curvature_fourier ha d]
  unfold periodIntegral gaussianCurvatureIntegrand
  rw [←mul_sub]
  exact GaussianCurvatureTail.norm_full_sub_period_le ha le_rfl d

noncomputable def error (M : ℕ) (q : ℝ) : ℝ :=
  let v:=q*(1-q)
  let a:=(M:ℝ)*v
  let b:=((M-1:ℕ):ℝ)*v
  (4*(M:ℝ)*v*|1-2*q|/(3*Real.pi*b^3)+
    5*(M:ℝ)*v/(16*Real.sqrt (2*Real.pi)*b^3*Real.sqrt b))+
    1/(4*Real.sqrt (2*Real.pi)*a^2*Real.sqrt a)+
    (1/a+1/(Real.pi^2*a^2))*Real.exp (-a*Real.pi^2/2)

/-- Complete local error with the exact stage900 unshifted Gaussian. -/
theorem binomial_error (M : ℕ) (hM : 2≤M) (j : ℤ) {q : ℝ}
    (hv : 9/40≤q*(1-q)) :
    |curvature M j q-GaussianCurvatureFourier.curvature ((M:ℝ)*(q*(1-q)))
      ((j:ℝ)-M*q)|≤error M q := by
  have hv0 : 0<q*(1-q) := by linarith
  have hM0 : 0<(M:ℝ) := by exact_mod_cast (show 0<M by omega)
  have ha : 0<(M:ℝ)*(q*(1-q)) := mul_pos hM0 hv0
  let d : ℝ := (j:ℝ)-M*q
  let A:=periodIntegral (actualCurvatureIntegrand M q d)
  let B:=periodIntegral (latticeGaussianIntegrand ((M:ℝ)*(q*(1-q))) d)
  let C:=periodIntegral (gaussianCurvatureIntegrand ((M:ℝ)*(q*(1-q))) d)
  let D : ℂ:=GaussianCurvatureFourier.curvature ((M:ℝ)*(q*(1-q))) d
  have he : |curvature M j q-GaussianCurvatureFourier.curvature ((M:ℝ)*(q*(1-q))) d|=‖A-D‖ := by
    dsimp [A,D,curvature]
    rw [←binomial_curvature_eq_periodIntegral,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  rw [he]
  have htri := norm_sub_le_norm_sub_add_norm_sub A B D
  have htri2 := norm_sub_le_norm_sub_add_norm_sub B C D
  have h1 := bernoulli_period_difference_bound M hM hv d
  have h2 := triangular_unshifted_period_bound ha d
  have h3 := gaussian_unshifted_period_bound ha d
  change ‖A-B‖≤_ at h1
  change ‖B-C‖≤_ at h2
  change ‖C-D‖≤_ at h3
  dsimp only [error]
  linarith

/-- A curvature coefficient on any positive-variance binomial, without a
near-symmetry hypothesis. This prices every non-bottom bad layer. -/
theorem abs_curvature_le (M : ℕ) (hM : 0<M) (j : ℤ) {q : ℝ}
    (hv : 0<q*(1-q)) :
    |curvature M j q|≤Real.pi^3/
      (8*Real.sqrt (2*Real.pi)*((M:ℝ)*(q*(1-q)))*Real.sqrt ((M:ℝ)*(q*(1-q)))) := by
  have hMr : 0<(M:ℝ) := by exact_mod_cast hM
  let a : ℝ := 4*(M:ℝ)*(q*(1-q))/Real.pi^2
  have ha : 0<a := by dsimp [a]; positivity
  have hb := norm_periodIntegral_le_even ha (by norm_num : (0:ℝ)≤1) 1
    (f:=actualCurvatureIntegrand M q ((j:ℝ)-M*q))
    (by unfold actualCurvatureIntegrand BinomialCurvatureError.oscillation centeredBernoulliCharacteristic TriangularGaussian.kernel; fun_prop) ?_
  · rw [show 2*1=2 by decide,GaussianKernelMoments.integral_second_fourier ha,one_mul,
      ←binomial_curvature_eq_periodIntegral,Complex.norm_real,Real.norm_eq_abs] at hb
    change |curvature M j q|≤_ at hb
    apply hb.trans_eq
    have hs : Real.sqrt a=2*Real.sqrt ((M:ℝ)*(q*(1-q)))/Real.pi := by
      dsimp [a]
      rw [show 4*(M:ℝ)*(q*(1-q))=4*((M:ℝ)*(q*(1-q))) by ring,
        Real.sqrt_div (by positivity),Real.sqrt_mul (by norm_num : (0:ℝ)≤4),
        Real.sqrt_sq Real.pi_pos.le]
      norm_num
    rw [hs]
    dsimp [a]
    field_simp
    ring
  · intro t ht
    rw [actualCurvatureIntegrand,norm_mul,norm_mul,norm_oscillation,one_mul,
      Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg t) (TriangularGaussian.kernel_nonneg t))]
    have hk : t^2*TriangularGaussian.kernel t≤t^2 := by
      nlinarith [sq_nonneg t,TriangularGaussian.kernel_le_one t]
    have he := centeredBernoulliCharacteristic_pow_norm_le_periodGaussian M hv.le (abs_le.mpr ht)
    calc
      _ ≤ t^2*Real.exp (-2*(M:ℝ)*(q*(1-q))*t^2/Real.pi^2) :=
        mul_le_mul hk he (norm_nonneg _) (sq_nonneg t)
      _ = _ := by
        simp only [one_mul,show 2*1=2 by decide]
        dsimp [a]
        congr 2
        ring

theorem mass_pair_le_one (M : ℕ) (i j : ℤ) (hij : i≠j) {q : ℝ}
    (hq0 : 0≤q) (hq1 : q≤1) : binomialMass M i q+binomialMass M j q≤1 := by
  by_cases hi : 0 ≤ i ∧ i ≤ (M:ℤ)
  · by_cases hj : 0≤j ∧ j≤(M:ℤ)
    · have hne : i.toNat≠j.toNat := by omega
      have hsub : ({i.toNat,j.toNat}:Finset ℕ)⊆Finset.range (M+1) := by
        intro n hn
        simp only [Finset.mem_insert,Finset.mem_singleton] at hn
        rcases hn with rfl|rfl <;> simp only [Finset.mem_range] <;> omega
      have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n _ _=>binomialMass_nonneg M (n:ℤ) hq0 hq1)
      have hei : (i.toNat:ℤ)=i := by omega
      have hej : (j.toNat:ℤ)=j := by omega
      simpa only [Finset.sum_pair hne,hei,hej,ReciprocalGradientBudget.sum_binomialMass] using hh
    · simpa only [binomialMass,if_neg hj,add_zero] using
        ReciprocalGradientBudget.binomialMass_le_one M i hq0 hq1
  · have he : binomialMass M i q=0 := by simp [binomialMass,hi]
    rw [he,zero_add]
    exact ReciprocalGradientBudget.binomialMass_le_one M j hq0 hq1

theorem curvature_ge_neg_one (M : ℕ) (j : ℤ) {q : ℝ} (hq0 : 0≤q) (hq1 : q≤1) :
    -1≤curvature M j q := by
  have hh := mass_pair_le_one M (j-1) (j+1) (by omega) hq0 hq1
  have h0 := binomialMass_nonneg M j hq0 hq1
  dsimp [curvature]
  linarith

variable {V : Type*} [DecidableEq V]

/-- Arithmetic curvature of actual probabilities; the natural predecessor
is guarded by k≥1, while all conditional binomial indices stay in ℤ. -/
theorem actual_curvature_eq_layer (G : SimpleGraph V) (S I : Finset V)
    (hIS : I⊆S) (hI : G.IsIndepSet (I:Set V)) {z : ℝ} (hz : 0<z)
    (k : ℕ) (hk : 1≤k) :
    2*tiltedProbability (countIndependent G S) z (partitionFunction G S z) k-
      tiltedProbability (countIndependent G S) z (partitionFunction G S z) (k-1)-
      tiltedProbability (countIndependent G S) z (partitionFunction G S z) (k+1)=
    hardCoreLayerExpectation G S I z (fun j M=>curvature M ((k:ℤ)-j) (z/(1+z))) := by
  have hm (j : ℕ) : ((k-1:ℕ):ℤ)-(j:ℤ)=((k:ℤ)-j)-1 := by omega
  have hp (j : ℕ) : ((k+1:ℕ):ℤ)-(j:ℤ)=((k:ℤ)-j)+1 := by omega
  simp only [tiltedProbability_eq_binomial_mixture G S I hIS hI hz,
    hardCoreLayerExpectation,curvature,hm,hp,mul_sub,Finset.sum_sub_distrib]
  congr 2
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro M hM
  ring

noncomputable def badCost (q : ℝ) (cuts : ℕ→ℝ) (n : ℕ) (M : ℕ) : ℝ :=
  (if (M:ℝ)<cuts 0 then 1 else 0)+
  ∑i∈Finset.range (n+1),
    (Real.pi^3/(8*Real.sqrt (2*Real.pi)*(cuts i*(q*(1-q)))*
      Real.sqrt (cuts i*(q*(1-q))))) *
    (if cuts i ≤ (M:ℝ) ∧ (M:ℝ)<cuts (i+1) then 1 else 0)

/-- Bad layers use the actual bottom mass and actual disjoint slice masses.
No assumptions about conditional independence of these events occur. -/
theorem curvature_lower_of_slices (G : SimpleGraph V) (S I : Finset V)
    (hIS : I⊆S) (hI : G.IsIndepSet (I:Set V)) {z cutoff : ℝ} (hz : 0<z)
    (k : ℕ) (hk : 1≤k) (hcut : 2≤cutoff)
    (hv : 9/40≤(z/(1+z))*(1-z/(1+z)))
    (cuts : ℕ→ℝ) (n : ℕ) (hstart : 0<cuts 0) (hend : cuts (n+1)=cutoff)
    (hsteps : ∀i ≤ n,cuts i ≤ cuts (i+1)) :
    hardCoreLayerExpectation G S I z (fun j M=>if cutoff≤(M:ℝ) then
      GaussianCurvatureFourier.curvature ((M:ℝ)*((z/(1+z))*(1-z/(1+z))))
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
      (Real.pi^3/(8*Real.sqrt (2*Real.pi)*(cuts i*(q*(1-q)))*
      Real.sqrt (cuts i*(q*(1-q))))) *
      (if cuts i ≤ (M:ℝ) ∧ (M:ℝ)<cuts (i+1) then 1 else 0) := by
    have hcp := hci i (by simp only [Finset.mem_range] at hi; omega)
    split_ifs <;> positivity
  have hsum := Finset.sum_nonneg hterm
  have hbad0 : 0≤badCost q cuts n M := by
    dsimp [badCost]
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
    · have hb : 1≤badCost q cuts n M := by simpa only [badCost,if_pos hbottom] using (le_add_of_nonneg_right hsum : (1:ℝ)≤1+_)
      linarith [curvature_ge_neg_one M ((k:ℤ)-j) hq0 hq1]
    · obtain ⟨i,hi,hilo,hihi⟩ := NegativePowerLayerBudget.exists_cut_interval cuts n
        (le_of_not_gt hbottom) (hend ▸ lt_of_not_ge hgood)
      have hcp:=hci i (by omega)
      have hMp : 0<(M:ℝ) := hcp.trans_le hilo
      have hMN : 0<M := by exact_mod_cast hMp
      have hab := (abs_le.mp (abs_curvature_le M hMN ((k:ℤ)-j) hv0)).1
      have hden : cuts i*(q*(1-q))≤(M:ℝ)*(q*(1-q)) := mul_le_mul_of_nonneg_right hilo hv0.le
      have hprice : Real.pi^3/(8*Real.sqrt (2*Real.pi)*((M:ℝ)*(q*(1-q)))*Real.sqrt ((M:ℝ)*(q*(1-q))))≤
          Real.pi^3/(8*Real.sqrt (2*Real.pi)*(cuts i*(q*(1-q)))*Real.sqrt (cuts i*(q*(1-q)))) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        gcongr
      have hsingle := Finset.single_le_sum hterm (Finset.mem_range.mpr (by omega : i<n+1))
      simp only [if_pos (And.intro hilo hihi),mul_one] at hsingle
      have hb : Real.pi^3/(8*Real.sqrt (2*Real.pi)*(cuts i*(q*(1-q)))*Real.sqrt (cuts i*(q*(1-q))))≤badCost q cuts n M := by
        simpa only [badCost,if_neg hbottom,zero_add] using hsingle
      linarith

private theorem power_five_halves {x : ℝ} (hx : 0<x) :
    x^(5/2:ℝ)=x^2*Real.sqrt x := by
  rw [show (5/2:ℝ)=(2:ℕ)+(1/2:ℝ) by norm_num,Real.rpow_add hx,
    Real.rpow_natCast,←Real.sqrt_eq_rpow]

private theorem power_seven_halves {x : ℝ} (hx : 0<x) :
    x^(7/2:ℝ)=x^3*Real.sqrt x := by
  rw [show (7/2:ℝ)=(3:ℕ)+(1/2:ℝ) by norm_num,Real.rpow_add hx,
    Real.rpow_natCast,←Real.sqrt_eq_rpow]

private theorem second_source_identity {x y v : ℝ} (hx : 0<x) (hy : 0<y) (hv : 0<v) :
    5*x*v/(16*Real.sqrt (2*Real.pi)*(y*v)^3*Real.sqrt (y*v))=
    (5/16)*(x/y)^(7/2:ℝ)/(Real.sqrt (2*Real.pi)*(x*v)^(5/2:ℝ)) := by
  rw [power_seven_halves (div_pos hx hy),power_five_halves (mul_pos hx hv),
    Real.sqrt_div hx.le,Real.sqrt_mul hy.le,Real.sqrt_mul hx.le,div_pow,mul_pow,mul_pow]
  have hxS : Real.sqrt x≠0 := ne_of_gt (Real.sqrt_pos.mpr hx)
  have hyS : Real.sqrt y≠0 := ne_of_gt (Real.sqrt_pos.mpr hy)
  have hvS : Real.sqrt v≠0 := ne_of_gt (Real.sqrt_pos.mpr hv)
  field_simp [hx.ne',hy.ne',hv.ne',hxS,hyS,hvS]

noncomputable def gaussianTail (a : ℝ) : ℝ :=
  (1/a+1/(Real.pi^2*a^2))*Real.exp (-a*Real.pi^2/2)

theorem error_eq_source (M : ℕ) (hM : 2≤M) {q : ℝ} (hv : 0<q*(1-q)) :
    error M q=
    4*|1-2*q| *((M:ℝ)/((M:ℝ)-1))^3/(3*Real.pi*((M:ℝ)*(q*(1-q)))^2)+
    ((5/16)*((M:ℝ)/((M:ℝ)-1))^(7/2:ℝ)+1/4)/
      (Real.sqrt (2*Real.pi)*((M:ℝ)*(q*(1-q)))^(5/2:ℝ))+
    gaussianTail ((M:ℝ)*(q*(1-q))) := by
  have hm : 0<(M:ℝ) := by exact_mod_cast (show 0<M by omega)
  have hn : 0<((M-1:ℕ):ℝ) := by exact_mod_cast (show 0<M-1 by omega)
  have hsub : ((M-1:ℕ):ℝ)=(M:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1≤M)]; norm_num
  dsimp only [error]
  rw [second_source_identity hm hn hv,hsub]
  have hfirst : 4*(M:ℝ)*(q*(1-q))*|1-2*q|/
      (3*Real.pi*(((M:ℝ)-1)*(q*(1-q)))^3)=
      4*|1-2*q| *((M:ℝ)/((M:ℝ)-1))^3/(3*Real.pi*((M:ℝ)*(q*(1-q)))^2) := by
    field_simp
  rw [hfirst]
  have hthird : 1/(4*Real.sqrt (2*Real.pi)*((M:ℝ)*(q*(1-q)))^2*
      Real.sqrt ((M:ℝ)*(q*(1-q))))=
      (1/4)/(Real.sqrt (2*Real.pi)*((M:ℝ)*(q*(1-q)))^(5/2:ℝ)) := by
    rw [power_five_halves (mul_pos hm hv)]
    field_simp
  rw [hthird]
  unfold gaussianTail
  ring

noncomputable def costTwo (alpha m vminus eta : ℝ) : ℝ :=
  (4*eta*PointMassErrorEnvelope.rho alpha m^3/(3*Real.pi))/(vminus*m)^2

noncomputable def costFiveHalves (alpha m vminus : ℝ) : ℝ :=
  (((5/16)*PointMassErrorEnvelope.rho alpha m^(7/2:ℝ)+1/4)/Real.sqrt (2*Real.pi))/
    (vminus*m)^(5/2:ℝ)

noncomputable def averagedError (alpha m vminus eta D : ℝ) : ℝ :=
  costTwo alpha m vminus eta*(1+NegativePowerHermite.coefficient 2 alpha*D/m)+
  costFiveHalves alpha m vminus*(1+NegativePowerHermite.coefficient (5/2) alpha*D/m)+
  gaussianTail (vminus*(alpha*m))

theorem gaussianTail_nonneg {a : ℝ} (ha : 0<a) : 0≤gaussianTail a := by
  unfold gaussianTail
  positivity

theorem gaussianTail_antitone {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    gaussianTail b≤gaussianTail a := by
  have hb := ha.trans_le hab
  have h1 : 1/b≤1/a := one_div_le_one_div_of_le ha hab
  have h2 : 1/(Real.pi^2*b^2)≤1/(Real.pi^2*a^2) := by
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
  have he : Real.exp (-b*Real.pi^2/2)≤Real.exp (-a*Real.pi^2/2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hab (sq_nonneg Real.pi)]
  exact mul_le_mul (add_le_add h1 h2) he (Real.exp_pos _).le (by positivity)

theorem error_le_power_envelope (M : ℕ) {q alpha m vminus eta : ℝ}
    (hm : 0<m) (ham : 1<alpha*m) (hM : alpha*m≤(M:ℝ))
    (hvm : 0<vminus) (hv : vminus≤q*(1-q)) (heta : |1-2*q|≤eta) :
    error M q≤costTwo alpha m vminus eta*((M:ℝ)/m)^(-2:ℝ)+
      costFiveHalves alpha m vminus*((M:ℝ)/m)^(-(5/2:ℝ))+
      gaussianTail (vminus*(alpha*m)) := by
  have hM0 : 0<(M:ℝ) := by linarith
  have hM1 : 1<M := by exact_mod_cast (ham.trans_le hM)
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
      (((5/16)*PointMassErrorEnvelope.rho alpha m^(7/2:ℝ)+1/4)/Real.sqrt (2*Real.pi))/
        ((M:ℝ)*vminus)^(5/2:ℝ) := by
    unfold costFiveHalves
    rw [PointMassErrorEnvelope.scaled_power_cost hM0 hm hvm]
  rw [error_eq_source M (by omega) hv0,hcost2,hcost52]
  have hfirst : 4*|1-2*q| *((M:ℝ)/((M:ℝ)-1))^3/(3*Real.pi*((M:ℝ)*(q*(1-q)))^2)≤
      (4*eta*PointMassErrorEnvelope.rho alpha m^3/(3*Real.pi))/((M:ℝ)*vminus)^2 := by
    rw [div_div]
    apply div_le_div₀ (by positivity) ?_ (by positivity) ?_
    · gcongr
    · gcongr
  have hsecond : ((5/16)*((M:ℝ)/((M:ℝ)-1))^(7/2:ℝ)+1/4)/
      (Real.sqrt (2*Real.pi)*((M:ℝ)*(q*(1-q)))^(5/2:ℝ))≤
      (((5/16)*PointMassErrorEnvelope.rho alpha m^(7/2:ℝ)+1/4)/Real.sqrt (2*Real.pi))/
        ((M:ℝ)*vminus)^(5/2:ℝ) := by
    rw [div_div]
    apply div_le_div₀ (by positivity) ?_ (by positivity) ?_ <;> gcongr
  have htail := gaussianTail_antitone (show 0<vminus*(alpha*m) by positivity)
    (show vminus*(alpha*m)≤(M:ℝ)*(q*(1-q)) by nlinarith [mul_le_mul hM hv hvm.le hM0.le])
  exact add_le_add (add_le_add hfirst hsecond) htail

/-- Actual J_2 and J_(5/2) are supplied by the negative-power Hermite theorem,
with no replacement of the random denominator by its mean. -/
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
  have htail := gaussianTail_nonneg (show 0<vminus*(alpha*m) by positivity)
  have hp := layer_mono G S I hz
    (fun _ M=>if alpha*m≤(M:ℝ) then error M (z/(1+z)) else 0)
    (fun _ M=>costTwo alpha m vminus eta*(if alpha*m≤(M:ℝ) then ((M:ℝ)/m)^(-2:ℝ) else 0)+
      costFiveHalves alpha m vminus*(if alpha*m≤(M:ℝ) then ((M:ℝ)/m)^(-(5/2:ℝ)) else 0)+
      gaussianTail (vminus*(alpha*m))) (by
        intro j M
        by_cases hgood : alpha*m≤(M:ℝ)
        · simpa only [if_pos hgood] using error_le_power_envelope M hm0 ham hgood hvm hv heta
        · simpa only [if_neg hgood,mul_zero,zero_add] using htail)
  rw [layer_add,layer_add,layer_const_mul,layer_const_mul,
    layer_const G S I hIS hI hz] at hp
  have h2 := single_hermite_layer_bound G S I hIS hI hz hm hm0 (by norm_num : (0:ℝ)<2) ha ha1 hvar
  have h52 := single_hermite_layer_bound G S I hIS hI hz hm hm0 (by norm_num : (0:ℝ)<5/2) ha ha1 hvar
  exact hp.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left h2 hc2)
    (mul_le_mul_of_nonneg_left h52 hc52)) le_rfl)

noncomputable def badPrice (q x : ℝ) : ℝ :=
  Real.pi^3/(8*Real.sqrt (2*Real.pi)*(x*(q*(1-q)))*Real.sqrt (x*(q*(1-q))))

theorem badPrice_nonneg {q x : ℝ} (hv : 0<q*(1-q)) (hx : 0<x) : 0≤badPrice q x := by
  unfold badPrice
  positivity

theorem badPrice_antitone {q x y : ℝ} (hv : 0<q*(1-q)) (hx : 0<x) (hxy : x≤y) :
    badPrice q y≤badPrice q x := by
  have hy:=hx.trans_le hxy
  unfold badPrice
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  gcongr

theorem bad_cost_layer_eq (G : SimpleGraph V) (S I : Finset V) (z : ℝ)
    (cuts : ℕ→ℝ) (n : ℕ) :
    hardCoreLayerExpectation G S I z (fun _ M=>badCost (z/(1+z)) cuts n M)=
      hardCoreAvailableLowerTail G S I z (cuts 0)+
      ∑i∈Finset.range (n+1),badPrice (z/(1+z)) (cuts i)*
        hardCoreAvailableSlice G S I z (cuts i) (cuts (i+1)) := by
  unfold badCost
  rw [layer_add,layer_sum]
  simp only [layer_const_mul,badPrice,hardCoreAvailableLowerTail,hardCoreAvailableSlice]

theorem slice_le_tail (G : SimpleGraph V) (S I : Finset V) {z lo hi : ℝ}
    (hz : 0≤z) (hlohi : lo≤hi) :
    hardCoreAvailableSlice G S I z lo hi ≤ hardCoreAvailableLowerTail G S I z hi := by
  rw [hardCoreAvailableSlice_eq_tail_sub G S I z hlohi]
  linarith [hardCoreAvailableLowerTail_nonneg G S I hz lo]

/-- Exact cumulative charging of all disjoint bad slices. -/
theorem bad_cost_layer_cumulative (G : SimpleGraph V) (S I : Finset V) {z : ℝ}
    (hz : 0≤z) (hv : 0<(z/(1+z))*(1-z/(1+z)))
    (cuts bound : ℕ→ℝ) (n : ℕ) (hstart : 0<cuts 0)
    (hsteps : ∀i ≤ n,cuts i ≤ cuts (i+1))
    (hbound : ∀i ≤ n+1,hardCoreAvailableLowerTail G S I z (cuts i)≤bound i) :
    hardCoreLayerExpectation G S I z (fun _ M=>badCost (z/(1+z)) cuts n M)≤
      bound 0+badPrice (z/(1+z)) (cuts n)*bound (n+1)+
      ∑i∈Finset.range n,(badPrice (z/(1+z)) (cuts i)-badPrice (z/(1+z)) (cuts (i+1)))*bound (i+1) := by
  rw [bad_cost_layer_eq]
  have hci (i : ℕ) (hi : i ≤ n+1) : 0 < cuts i := hstart.trans_le
    (NegativePowerLayerBudget.cut_le_of_steps cuts n hsteps (Nat.zero_le i) hi)
  have hb:=hardCoreAvailableSlices_le_cumulative G S I hz cuts (fun i=>badPrice (z/(1+z)) (cuts i)) bound n
    hsteps (badPrice_nonneg hv hstart) (badPrice_nonneg hv (hci n (by omega)))
    (fun i hi=>badPrice_antitone hv (hci i (by omega)) (hsteps i (by omega)))
    (fun i hi=>hbound (i+1) (by omega))
  have h0:=hbound 0 (by omega)
  linarith

/-- The original stage900 per-slice charge, as a consequence of the same
true slice distribution. Tail bounds are never summed as disjoint events. -/
theorem bad_cost_layer_bound (G : SimpleGraph V) (S I : Finset V) {z : ℝ}
    (hz : 0≤z) (hv : 0<(z/(1+z))*(1-z/(1+z)))
    (cuts bound : ℕ→ℝ) (n : ℕ) (hstart : 0<cuts 0)
    (hsteps : ∀i ≤ n,cuts i ≤ cuts (i+1))
    (hbound : ∀i ≤ n+1,hardCoreAvailableLowerTail G S I z (cuts i)≤bound i) :
    hardCoreLayerExpectation G S I z (fun _ M=>badCost (z/(1+z)) cuts n M)≤
      bound 0+∑i∈Finset.range (n+1),badPrice (z/(1+z)) (cuts i)*bound (i+1) := by
  rw [bad_cost_layer_eq]
  apply add_le_add (hbound 0 (by omega))
  apply Finset.sum_le_sum
  intro i hi
  have hin : i<n+1 := Finset.mem_range.mp hi
  have hci : 0 < cuts i := hstart.trans_le
    (NegativePowerLayerBudget.cut_le_of_steps cuts n hsteps (Nat.zero_le i) (by omega))
  exact mul_le_mul_of_nonneg_left ((slice_le_tail G S I hz (hsteps i (by omega))).trans
    (hbound (i+1) (by omega))) (badPrice_nonneg hv hci)

/-- The complete actual probability-curvature lower bound. Local binomial
errors and bad-layer curvature are proved, not supplied as hypotheses. -/
theorem actual_curvature_lower (G : SimpleGraph V) (S I : Finset V)
    (hIS : I⊆S) (hI : G.IsIndepSet (I:Set V)) {z alpha m vminus eta D : ℝ}
    (hz : 0<z) (hm : m=hardCoreAvailableMean G S I z) (hm0 : 0<m)
    (ha : 0<alpha) (ha1 : alpha<1) (ham : 2≤alpha*m)
    (hvm : 0<vminus) (hv : vminus≤(z/(1+z))*(1-z/(1+z)))
    (hnear : 9/40≤(z/(1+z))*(1-z/(1+z)))
    (heta : |1-2*(z/(1+z))|≤eta)
    (hvar : hardCoreAvailableVariance G S I z≤D*m)
    (k : ℕ) (hk : 1≤k) (cuts bound : ℕ→ℝ) (n : ℕ)
    (hstart : 0<cuts 0) (hend : cuts (n+1)=alpha*m)
    (hsteps : ∀i ≤ n,cuts i ≤ cuts (i+1))
    (hbound : ∀i ≤ n+1,hardCoreAvailableLowerTail G S I z (cuts i)≤bound i) :
    hardCoreLayerExpectation G S I z (fun j M=>if alpha*m≤(M:ℝ) then
      GaussianCurvatureFourier.curvature ((M:ℝ)*((z/(1+z))*(1-z/(1+z))))
        ((k:ℝ)-binomialLayerMean j M z) else 0)-
      averagedError alpha m vminus eta D-
      (bound 0+∑i∈Finset.range (n+1),badPrice (z/(1+z)) (cuts i)*bound (i+1))≤
    2*tiltedProbability (countIndependent G S) z (partitionFunction G S z) k-
      tiltedProbability (countIndependent G S) z (partitionFunction G S z) (k-1)-
      tiltedProbability (countIndependent G S) z (partitionFunction G S z) (k+1) := by
  have h1:=curvature_lower_of_slices G S I hIS hI hz k hk ham hnear cuts n hstart hend hsteps
  have h2:=error_layer_bound G S I hIS hI hz.le hm hm0 ha ha1 (by linarith) hvm hv heta hvar
  have h3:=bad_cost_layer_bound G S I hz.le (hvm.trans_le hv) cuts bound n hstart hsteps hbound
  linarith

noncomputable def scale (v m : ℝ) : ℝ := Real.sqrt (2*Real.pi)*(v*m)*Real.sqrt (v*m)

noncomputable def normalizedError (alpha m v eta D : ℝ) : ℝ :=
  (4*Real.sqrt (2*Real.pi)/(3*Real.pi))*eta*PointMassErrorEnvelope.rho alpha m^3*
      (1+NegativePowerHermite.coefficient 2 alpha*D/m)/Real.sqrt (v*m)+
  ((5/16)*PointMassErrorEnvelope.rho alpha m^(7/2:ℝ)+1/4)*
      (1+NegativePowerHermite.coefficient (5/2) alpha*D/m)/(v*m)+
  scale v m*gaussianTail (v*(alpha*m))

theorem scale_averagedError {v m : ℝ} (hv : 0<v) (hm : 0<m) (alpha eta D : ℝ) :
    scale v m*averagedError alpha m v eta D=normalizedError alpha m v eta D := by
  have hvm:=mul_pos hv hm
  have hs : Real.sqrt (v*m)≠0 := (Real.sqrt_pos.mpr hvm).ne'
  have hpi : Real.sqrt (2*Real.pi)≠0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hsq : Real.sqrt (v*m)^2=v*m := Real.sq_sqrt hvm.le
  unfold averagedError normalizedError costTwo costFiveHalves scale
  rw [power_five_halves hvm]
  field_simp [hv.ne',hm.ne',hs,hpi]
  ring_nf
  rw [hsq]
  ring

/-- The explicit Gaussian tail price at any positive frequency cutoff. -/
noncomputable def frequencyTail (a T : ℝ) : ℝ :=
  ((T/a+1/(a^2*T))/Real.pi)*Real.exp (-a*T^2/2)

theorem frequencyTail_nonneg {a T : ℝ} (ha : 0<a) (hT : 0<T) :
    0≤frequencyTail a T := by unfold frequencyTail; positivity

theorem frequencyTail_pi (a : ℝ) : frequencyTail a Real.pi=gaussianTail a := by
  unfold frequencyTail gaussianTail
  field_simp

theorem frequencyTail_antitone_cutoff {a T U : ℝ} (ha : 0<a) (hT : 0<T) (hTU : T≤U) :
    frequencyTail a U≤frequencyTail a T := by
  have hd (x : ℝ) (hx : 0<x) : HasDerivAt (frequencyTail a)
      (-(x^2+1/(a^2*x^2))/Real.pi*Real.exp (-a*x^2/2)) x := by
    unfold frequencyTail
    have hd1 := ((((hasDerivAt_id x).div_const a).add
      ((hasDerivAt_const x (1:ℝ)).div ((hasDerivAt_id x).const_mul (a^2)) (by positivity))).div_const Real.pi)
    have hd2 := (((((hasDerivAt_id x).pow 2).const_mul (-a)).div_const 2).exp)
    convert! hd1.mul hd2 using 1
    simp only [id_eq,Pi.add_apply,Pi.div_apply,Pi.pow_apply,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul]
    field_simp
    ring
  have hm : AntitoneOn (frequencyTail a) (Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · intro x hx
      exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hd x (by simpa only [interior_Ioi,Set.mem_Ioi] using hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx0 : 0<x := by simpa only [interior_Ioi,Set.mem_Ioi] using hx
      rw [(hd x hx0).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (by positivity)) Real.pi_pos.le) (Real.exp_pos _).le
  exact hm hT (hT.trans_le hTU) hTU

theorem frequencyTail_antitone_variance {a b T : ℝ} (ha : 0<a) (hab : a≤b) (hT : 0<T) :
    frequencyTail b T≤frequencyTail a T := by
  have hb:=ha.trans_le hab
  have h1 : T/b≤T/a := div_le_div_of_nonneg_left hT.le ha hab
  have h2 : 1/(b^2*T)≤1/(a^2*T) := by
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
  have he : Real.exp (-b*T^2/2)≤Real.exp (-a*T^2/2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hab (sq_nonneg T)]
  exact mul_le_mul (div_le_div_of_nonneg_right (add_le_add h1 h2) Real.pi_pos.le) he
    (Real.exp_pos _).le (by positivity)

/-- These are exactly the two finite tail prices retained in stage900.
The true-binomial tail is allowed even though our near-central theorem
already controls the entire period and does not need to pay it. -/
noncomputable def normalizedCutoffError (alpha m vminus vplus eta D T : ℝ) : ℝ :=
  (4*Real.sqrt (2*Real.pi)/(3*Real.pi))*eta*PointMassErrorEnvelope.rho alpha m^3*
      (1+NegativePowerHermite.coefficient 2 alpha*D/m)/Real.sqrt (vminus*m)+
  ((5/16)*PointMassErrorEnvelope.rho alpha m^(7/2:ℝ)+1/4)*
      (1+NegativePowerHermite.coefficient (5/2) alpha*D/m)/(vminus*m)+
  scale vplus m*(4*(1-T/Real.pi)*Real.exp (-vminus*(alpha*m)*T^2/2)+
    frequencyTail (vminus*(alpha*m)) T)

theorem normalizedError_le_cutoff {alpha m vminus v vplus eta D T : ℝ}
    (ha : 0<alpha) (ha1 : alpha<1) (hm : 0<m) (ham : 1<alpha*m)
    (hvm : 0<vminus) (hvv : vminus≤v) (hvp : v≤vplus)
    (heta : 0≤eta) (hD : 0≤D) (hT : 0<T) (hTpi : T≤Real.pi) :
    normalizedError alpha m v eta D≤normalizedCutoffError alpha m vminus vplus eta D T := by
  have hv:=hvm.trans_le hvv
  have hvplus:=hv.trans_le hvp
  have hr:=PointMassErrorEnvelope.rho_pos ham
  have hcoef2:=NegativePowerHermite.coefficient_lower (by norm_num : (0:ℝ)<2) ha ha1
  have hcoef52:=NegativePowerHermite.coefficient_lower (by norm_num : (0:ℝ)<5/2) ha ha1
  have hc2 : 0≤NegativePowerHermite.coefficient 2 alpha := by linarith
  have hc52 : 0≤NegativePowerHermite.coefficient (5/2) alpha := by norm_num at hcoef52; linarith
  have hfirst :
      (4*Real.sqrt (2*Real.pi)/(3*Real.pi))*eta*PointMassErrorEnvelope.rho alpha m^3*
        (1+NegativePowerHermite.coefficient 2 alpha*D/m)/Real.sqrt (v*m)≤
      (4*Real.sqrt (2*Real.pi)/(3*Real.pi))*eta*PointMassErrorEnvelope.rho alpha m^3*
        (1+NegativePowerHermite.coefficient 2 alpha*D/m)/Real.sqrt (vminus*m) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    gcongr
  have hsecond :
      ((5/16)*PointMassErrorEnvelope.rho alpha m^(7/2:ℝ)+1/4)*
        (1+NegativePowerHermite.coefficient (5/2) alpha*D/m)/(v*m)≤
      ((5/16)*PointMassErrorEnvelope.rho alpha m^(7/2:ℝ)+1/4)*
        (1+NegativePowerHermite.coefficient (5/2) alpha*D/m)/(vminus*m) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    gcongr
  have hgauss : gaussianTail (v*(alpha*m))≤frequencyTail (vminus*(alpha*m)) T := by
    rw [←frequencyTail_pi]
    exact (frequencyTail_antitone_cutoff (by positivity : 0<v*(alpha*m)) hT hTpi).trans
      (frequencyTail_antitone_variance (by positivity) (by gcongr) hT)
  have hscale : scale v m≤scale vplus m := by unfold scale; gcongr
  have htail := mul_le_mul hscale hgauss (gaussianTail_nonneg (by positivity))
    (show 0≤scale vplus m by unfold scale; positivity)
  have htrue : 0≤4*(1-T/Real.pi)*Real.exp (-vminus*(alpha*m)*T^2/2) := by
    have hh : T/Real.pi≤1 := (div_le_one Real.pi_pos).mpr hTpi
    positivity
  have hadd := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left htrue :
      frequencyTail (vminus*(alpha*m)) T≤4*(1-T/Real.pi)*Real.exp (-vminus*(alpha*m)*T^2/2)+
        frequencyTail (vminus*(alpha*m)) T)
    (show 0≤scale vplus m by unfold scale; positivity)
  exact add_le_add (add_le_add hfirst hsecond) (htail.trans hadd)

/-- A stronger full-period Gaussian tail convenient for exact numerical ASTs. -/
noncomputable def centralTail (m vminus vplus : ℝ) : ℝ :=
  Real.sqrt (2*Real.pi)*vplus*Real.sqrt vplus*
    (3*Real.sqrt m/vminus+1/(vminus^2*Real.sqrt m))*Real.exp (-(3/2)*vminus*m)

noncomputable def centralError (m vminus vplus eta D : ℝ) : ℝ :=
  (4*Real.sqrt (2*Real.pi)/(3*Real.pi))*eta*PointMassErrorEnvelope.rho (1/3) m^3*
      (1+NegativePowerHermite.coefficient 2 (1/3)*D/m)/Real.sqrt (vminus*m)+
  ((5/16)*PointMassErrorEnvelope.rho (1/3) m^(7/2:ℝ)+1/4)*
      (1+NegativePowerHermite.coefficient (5/2) (1/3)*D/m)/(vminus*m)+
  centralTail m vminus vplus

theorem scale_gaussianTail_le_central {m vminus vplus : ℝ}
    (hm : 0<m) (hvm : 0<vminus) (hvp : 0<vplus) :
    scale vplus m*gaussianTail (vminus*((1/3)*m))≤centralTail m vminus vplus := by
  have hpi : 9≤Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hsm : Real.sqrt m≠0 := (Real.sqrt_pos.mpr hm).ne'
  have hsq : Real.sqrt m^2=m := Real.sq_sqrt hm.le
  have hprice : scale vplus m*(1/(vminus*((1/3)*m))+1/(Real.pi^2*(vminus*((1/3)*m))^2))=
      Real.sqrt (2*Real.pi)*vplus*Real.sqrt vplus*
        (3*Real.sqrt m/vminus+9/(Real.pi^2*vminus^2*Real.sqrt m)) := by
    unfold scale
    rw [Real.sqrt_mul hvp.le]
    field_simp [hvm.ne',hm.ne',hsm]
    ring_nf
    rw [hsq]
    ring
  have hratio : 9/(Real.pi^2*vminus^2*Real.sqrt m)≤1/(vminus^2*Real.sqrt m) := by
    rw [show Real.pi^2*vminus^2*Real.sqrt m=Real.pi^2*(vminus^2*Real.sqrt m) by ring,←div_div]
    exact div_le_div_of_nonneg_right ((div_le_one (by positivity)).mpr hpi) (by positivity)
  have hbound := mul_le_mul_of_nonneg_left (add_le_add (le_refl (3*Real.sqrt m/vminus)) hratio)
    (show 0≤Real.sqrt (2*Real.pi)*vplus*Real.sqrt vplus by positivity)
  have he : Real.exp (-(vminus*((1/3)*m))*Real.pi^2/2)≤Real.exp (-(3/2)*vminus*m) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hpi (show 0≤vminus*m by positivity)]
  unfold gaussianTail centralTail
  rw [←mul_assoc,hprice]
  exact mul_le_mul hbound he (Real.exp_pos _).le (by positivity)

/-- The final central error uses the unshifted variance, the exact rho and
J_2/J_(5/2) corrections, and only the interval endpoints vminus/vplus. -/
theorem normalizedError_le_central {m vminus v vplus eta D : ℝ}
    (hm : 3<m) (hvm : 0<vminus) (hvv : vminus≤v) (hvp : v≤vplus)
    (heta : 0≤eta) (hD : 0≤D) :
    normalizedError (1/3) m v eta D≤centralError m vminus vplus eta D := by
  have hm0 : 0<m := by linarith
  have hh := normalizedError_le_cutoff (by norm_num : (0:ℝ)<1/3) (by norm_num : (1/3:ℝ)<1)
    hm0 (by linarith : 1<(1/3:ℝ)*m) hvm hvv hvp heta hD Real.pi_pos le_rfl
  have ht := scale_gaussianTail_le_central hm0 hvm ((hvm.trans_le hvv).trans_le hvp)
  apply hh.trans
  unfold normalizedCutoffError centralError
  rw [div_self Real.pi_ne_zero,sub_self,mul_zero,zero_mul,zero_add,frequencyTail_pi]
  exact add_le_add le_rfl ht

#print axioms normalizedError_le_central
#print axioms normalizedError_le_cutoff
#print axioms actual_curvature_lower
#print axioms scale_averagedError
#print axioms bad_cost_layer_cumulative
#print axioms error_eq_source
#print axioms error_layer_bound
#print axioms binomial_error
#print axioms abs_curvature_le
#print axioms curvature_lower_of_slices
end ForestUnimodality.CurvatureErrorLayerBudget
