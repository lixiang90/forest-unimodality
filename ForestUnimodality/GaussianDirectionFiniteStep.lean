import ForestUnimodality.GaussianFiniteStep
import ForestUnimodality.SignedGaussianShiftedLayerBudget

/-! A finite outward displacement of the Gaussian mixture uses the original
joint layer law. Mean matching removes the cross term for every displacement. -/
namespace ForestUnimodality.GaussianDirectionFiniteStep
open Finset Real Set NegativePowerLayerBudget SignedGaussianProfile SignedGaussianHermite
open ShiftedLayerMoments
variable {V : Type*} [DecidableEq V]

theorem offset_mean_zero (G : SimpleGraph V) (S I : Finset V)
    (hIS : I⊆S) (hI : G.IsIndepSet (I:Set V)) {z m k v : ℝ}
    (hz : 0<z) (hmean : hardCoreMean G S z=k) :
    hardCoreLayerExpectation G S I z (offset z m 0 k v)=0 := by
  have he : offset z m 0 k v=(fun j M=>(1/sqrt (v*m))*(k-binomialLayerMean j M z)) := by
    funext j M
    dsimp [offset]
    ring_nf
  rw [he,layer_const_mul,hardCoreLayerExpectation_centered_mean G S I hIS hI hz hmean,mul_zero]

theorem quadratic_shift (G : SimpleGraph V) (S I : Finset V)
    (hIS : I⊆S) (hI : G.IsIndepSet (I:Set V)) {z m k v : ℝ}
    (hz : 0<z) (hmean : hardCoreMean G S z=k) (H L a B t : ℝ) :
    hardCoreLayerExpectation G S I z (fun j M=>quadratic H L a B
      (ratio m 0 M) (offset z m 0 k v j M+t))=
    hardCoreLayerExpectation G S I z (fun j M=>quadratic H L a B
      (ratio m 0 M) (offset z m 0 k v j M))-a*t^2 := by
  have he (j M:ℕ) : quadratic H L a B (ratio m 0 M) (offset z m 0 k v j M+t)=
      quadratic H L a B (ratio m 0 M) (offset z m 0 k v j M)+
        (-2*a*t)*(offset z m 0 k v j M)-a*t^2 := by
    unfold ShiftedLayerMoments.quadratic
    ring_nf
  simp_rw [he]
  rw [layer_sub,layer_add,layer_const_mul,offset_mean_zero G S I hIS hI hz hmean,
    layer_const G S I hIS hI hz.le,mul_zero,add_zero]

theorem shifted_curvature_lower (G : SimpleGraph V) (S I : Finset V)
    (hIS : I⊆S) (hI : G.IsIndepSet (I:Set V))
    {z m k v R D gamma K alpha beta : ℝ}
    (hz : 0<z) (hm : m=hardCoreAvailableMean G S I z) (hm0 : 0<m)
    (hmean : hardCoreMean G S z=k) (hv : 0<v)
    (hR : 0≤R) (hD : 0≤D) (hg : 0<gamma) (hg3 : gamma<3)
    (ha : 0<alpha) (hab : alpha<beta) (hb1 : beta≤1)
    (hK : K≤coefficient gamma beta) (hKn : K≤0) (hL : 0≤first gamma 1)
    (hbad : profile gamma 1+first gamma 1*(alpha-1)+K*(alpha-1)^2≤0)
    (hvarL : hardCoreVariance G S z-(z/(1+z))*(1-z/(1+z))*m≤R*(v*m))
    (hvarM : hardCoreAvailableVariance G S I z≤D*m)
    (cuts U rate : ℕ→ℝ) (n : ℕ) (hstart : cuts 0=alpha) (hend : cuts (n+1)=beta)
    (hsteps : ∀i≤n,cuts i≤cuts (i+1))
    (hU : ∀i≤n,positiveGap gamma K (cuts i)≤U i)
    (hUdec : ∀i<n,U (i+1)≤U i) (hUlast : U (n+1)=0)
    (htail : ∀i≤n,hardCoreAvailableLowerTail G S I z (cuts (i+1)*m)≤exp (-m*rate i))
    (t : ℝ) :
    (profile gamma 1-(gamma/2)*R+K*D/m-
      (∑i∈range (n+1),(U i-U (i+1))*exp (-m*rate i)))-gamma*t^2/2≤
    hardCoreLayerExpectation G S I z (fun j M=>if alpha*m≤(M:ℝ) then
      SignedGaussianLayerBudget.kernel (ratio m 0 M) (offset z m 0 k v j M+t) else 0) := by
  have ha1 : alpha≤1 := hab.le.trans hb1
  have hUn (i:ℕ) (hi:i≤n) : 0≤U i := (le_max_left _ _).trans (hU i hi)
  have he (y w:ℝ) : SignedGaussianSlices.envelope gamma K y w=
      quadratic (profile gamma 1) (first gamma 1) (gamma/2) (-K) y w := by
    unfold SignedGaussianSlices.envelope SignedGaussianHermite.quadratic ShiftedLayerMoments.quadratic
    ring_nf
  have hp:=layer_mono G S I hz.le
    (fun j M=>quadratic (profile gamma 1) (first gamma 1) (gamma/2) (-K)
      (ratio m 0 M) (offset z m 0 k v j M+t)-
      (∑i∈range (n+1),U i*(if cuts i≤ratio m 0 M ∧ ratio m 0 M<cuts (i+1) then 1 else 0)))
    (fun j M=>if alpha*m≤(M:ℝ) then
      SignedGaussianLayerBudget.kernel (ratio m 0 M) (offset z m 0 k v j M+t) else 0) (by
    intro j M
    by_cases hM : alpha*m≤(M:ℝ)
    · rw [if_pos hM,←he]
      exact SignedGaussianSlices.lower_with_slices hg hg3 ha hab hb1 hK cuts U n
        hstart hend hsteps hU (ratio_good hm0 (by norm_num) ha1 hM) _
    · rw [if_neg hM]
      have hy : ratio m 0 M≤alpha := by
        simp only [ratio,add_zero]
        exact (div_le_iff₀ hm0).mpr (le_of_lt (lt_of_not_ge hM))
      have hq:=quadratic_nonpos_below (w:=offset z m 0 k v j M+t) hL
        (show 0≤gamma/2 by positivity) (neg_nonneg.mpr hKn) ha1 hy (by simpa using hbad)
      have hs : 0≤∑i∈range (n+1),U i*
        (if cuts i≤ratio m 0 M ∧ ratio m 0 M<cuts (i+1) then 1 else 0) := by
        apply sum_nonneg
        intro i hi
        exact mul_nonneg (hUn i (by have:=mem_range.mp hi;omega)) (by split_ifs <;> norm_num)
      linarith)
  rw [layer_sub,quadratic_shift G S I hIS hI hz hmean] at hp
  have hq:=quadratic_expectation_lower G S I hIS hI hz hm hm0 (c:=0) (by norm_num) hmean hv
    (show 0≤gamma/2 by positivity) (neg_nonneg.mpr hKn) hR hD hvarL hvarM
    (H:=profile gamma 1) (L:=first gamma 1)
  have hs:=SignedGaussianShiftedLayerBudget.slice_cost_le G S I hz.le hm0 (c:=0)
    (by norm_num) hb1 cuts U rate n hend hsteps hUn hUdec hUlast htail
  simp only [neg_mul,neg_div,sub_neg_eq_add] at hq
  linarith

theorem negative_second_eq_kernel {y : ℝ} (hy : 0<y) (x : ℝ) :
    -GaussianFiniteStep.second y x=SignedGaussianLayerBudget.kernel y x := by
  have hp : y^(-(3/2:ℝ))=y^(-(1/2:ℝ))/y := by
    rw [show (-(3/2):ℝ)=-(1/2:ℝ)+(-1) by norm_num,rpow_add hy,rpow_neg_one]
    ring_nf
  unfold GaussianFiniteStep.second GaussianFiniteStep.profile SignedGaussianLayerBudget.kernel
  rw [hp]
  field_simp
  ring_nf


noncomputable def retainedProfile (G : SimpleGraph V) (S I : Finset V)
    (z m alpha k v sigma t : ℝ) : ℝ :=
  hardCoreLayerExpectation G S I z (fun j M=>if alpha*m≤(M:ℝ) then
    GaussianFiniteStep.profile (ratio m 0 M) (offset z m 0 k v j M+sigma*t) else 0)

noncomputable def retainedFirst (G : SimpleGraph V) (S I : Finset V)
    (z m alpha k v sigma t : ℝ) : ℝ :=
  hardCoreLayerExpectation G S I z (fun j M=>if alpha*m≤(M:ℝ) then
    sigma*GaussianFiniteStep.first (ratio m 0 M) (offset z m 0 k v j M+sigma*t) else 0)

noncomputable def retainedSecond (G : SimpleGraph V) (S I : Finset V)
    (z m alpha k v sigma t : ℝ) : ℝ :=
  hardCoreLayerExpectation G S I z (fun j M=>if alpha*m≤(M:ℝ) then
    GaussianFiniteStep.second (ratio m 0 M) (offset z m 0 k v j M+sigma*t) else 0)

theorem hasDerivAt_retainedProfile (G : SimpleGraph V) (S I : Finset V)
    (z m alpha k v sigma t : ℝ) :
    HasDerivAt (retainedProfile G S I z m alpha k v sigma)
      (retainedFirst G S I z m alpha k v sigma t) t := by
  unfold retainedProfile retainedFirst hardCoreLayerExpectation
  apply HasDerivAt.fun_sum
  intro j _
  apply HasDerivAt.fun_sum
  intro M _
  by_cases hM : alpha*m≤(M:ℝ)
  · simp only [if_pos hM]
    apply (((GaussianFiniteStep.hasDerivAt_profile (ratio m 0 M)
      (offset z m 0 k v j M+sigma*t)).comp t
      (((hasDerivAt_id t).const_mul sigma).const_add (offset z m 0 k v j M))).const_mul
      (hardCoreLayerWeight G S I z j M)).congr_deriv
    ring_nf
  · simp only [if_neg hM,mul_zero]
    exact hasDerivAt_const t 0

theorem hasDerivAt_retainedFirst (G : SimpleGraph V) (S I : Finset V)
    (z m alpha k v sigma t : ℝ) (hsigma : sigma^2=1) :
    HasDerivAt (retainedFirst G S I z m alpha k v sigma)
      (retainedSecond G S I z m alpha k v sigma t) t := by
  unfold retainedFirst retainedSecond hardCoreLayerExpectation
  apply HasDerivAt.fun_sum
  intro j _
  apply HasDerivAt.fun_sum
  intro M _
  by_cases hM : alpha*m≤(M:ℝ)
  · simp only [if_pos hM]
    apply ((((GaussianFiniteStep.hasDerivAt_first (ratio m 0 M)
      (offset z m 0 k v j M+sigma*t)).comp t
      (((hasDerivAt_id t).const_mul sigma).const_add (offset z m 0 k v j M))).const_mul sigma).const_mul
      (hardCoreLayerWeight G S I z j M)).congr_deriv
    calc
      _=(hardCoreLayerWeight G S I z j M*
        GaussianFiniteStep.second (ratio m 0 M) (offset z m 0 k v j M+sigma*t))*sigma^2 := by ring_nf
      _=_ := by rw [hsigma,mul_one]
  · simp only [if_neg hM,mul_zero]
    exact hasDerivAt_const t 0

theorem retainedSecond_eq (G : SimpleGraph V) (S I : Finset V)
    {z m alpha k v sigma t : ℝ} (hm : 0<m) (ha : 0<alpha) :
    -retainedSecond G S I z m alpha k v sigma t=
      hardCoreLayerExpectation G S I z (fun j M=>if alpha*m≤(M:ℝ) then
        SignedGaussianLayerBudget.kernel (ratio m 0 M) (offset z m 0 k v j M+sigma*t) else 0) := by
  rw [show -retainedSecond G S I z m alpha k v sigma t=
    (-1)*retainedSecond G S I z m alpha k v sigma t by ring_nf]
  unfold retainedSecond
  rw [←layer_const_mul]
  congr 1
  funext j M
  by_cases hM : alpha*m≤(M:ℝ)
  · simp only [if_pos hM,neg_one_mul]
    have hy : 0<ratio m 0 M := by
      simp only [ratio,add_zero]
      exact div_pos ((mul_pos ha hm).trans_le hM) hm
    exact negative_second_eq_kernel hy _
  · simp [hM]

/-- Both outward signs are allowed, and every intermediate displacement
is controlled using the same mean-matched graph law. -/
theorem actual_finite_step (G : SimpleGraph V) (S I : Finset V)
    {z m alpha k v sigma h B gamma : ℝ} (hm : 0<m) (ha : 0<alpha)
    (hsigma : sigma^2=1) (hh : 0≤h)
    (hcurv : ∀t:ℝ,B-gamma*t^2/2≤
      hardCoreLayerExpectation G S I z (fun j M=>if alpha*m≤(M:ℝ) then
        SignedGaussianLayerBudget.kernel (ratio m 0 M) (offset z m 0 k v j M+t) else 0)) :
    B*h^2/2-gamma*h^4/24≤
      retainedProfile G S I z m alpha k v sigma 0-
      retainedProfile G S I z m alpha k v sigma h+
      h*retainedFirst G S I z m alpha k v sigma 0 := by
  apply GaussianFiniteStep.finite_step_lower hh
    (fun t _=>hasDerivAt_retainedProfile G S I z m alpha k v sigma t)
    (fun t _=>hasDerivAt_retainedFirst G S I z m alpha k v sigma t hsigma)
  intro t ht
  rw [retainedSecond_eq G S I hm ha]
  have hq:=hcurv (sigma*t)
  simpa only [mul_pow,hsigma,one_mul] using hq


theorem kernel_profile {y : ℝ} (hy : 0<y) (x theta : ℝ) :
    GaussianDirectionalEnvelope.kernel y x theta=
      GaussianFiniteStep.profile y x+theta*GaussianFiniteStep.first y x := by
  unfold GaussianDirectionalEnvelope.kernel GaussianFiniteStep.first GaussianFiniteStep.profile
  rw [rpow_neg hy.le,←sqrt_eq_rpow]
  ring_nf

theorem retained_kernel_identity (G : SimpleGraph V) (S I : Finset V)
    {z m alpha k v sigma h r : ℝ} (hm : 0<m) (ha : 0<alpha) (hr : r≠1) :
    (1-r)*hardCoreLayerExpectation G S I z (fun j M=>if alpha*m≤(M:ℝ) then
      GaussianDirectionalEnvelope.kernel (ratio m 0 M) (offset z m 0 k v j M)
        (-r*sigma*h/(1-r)) else 0)=
      (1-r)*retainedProfile G S I z m alpha k v sigma 0-
        r*h*retainedFirst G S I z m alpha k v sigma 0 := by
  unfold retainedProfile retainedFirst
  rw [←layer_const_mul,←layer_const_mul,←layer_const_mul,←layer_sub]
  congr 1
  funext j M
  by_cases hM : alpha*m≤(M:ℝ)
  · simp only [if_pos hM,mul_zero,add_zero]
    have hy : 0<ratio m 0 M := by
      simp only [ratio,add_zero]
      exact div_pos ((mul_pos ha hm).trans_le hM) hm
    rw [kernel_profile hy]
    have hd : 1-r≠0 := sub_ne_zero.mpr hr.symm
    field_simp
    ring_nf
  · simp [hM]

theorem actual_direction_lower_of_curvature (G : SimpleGraph V) (S I : Finset V)
    {z m alpha k v sigma h B gamma r L : ℝ} (hm : 0<m) (ha : 0<alpha)
    (hsigma : sigma^2=1) (hh : 0≤h) (hr : 0≤r) (hr1 : r<1)
    (hcurv : ∀t:ℝ,B-gamma*t^2/2≤
      hardCoreLayerExpectation G S I z (fun j M=>if alpha*m≤(M:ℝ) then
        SignedGaussianLayerBudget.kernel (ratio m 0 M) (offset z m 0 k v j M+t) else 0))
    (hmain : L≤hardCoreLayerExpectation G S I z (fun j M=>if alpha*m≤(M:ℝ) then
      GaussianDirectionalEnvelope.kernel (ratio m 0 M) (offset z m 0 k v j M)
        (-r*sigma*h/(1-r)) else 0)) :
    L+(r/(1-r))*(B*h^2/2-gamma*h^4/24)≤
      (retainedProfile G S I z m alpha k v sigma 0-
        r*retainedProfile G S I z m alpha k v sigma h)/(1-r) := by
  have hd : 0<1-r := sub_pos.mpr hr1
  have hf:=actual_finite_step G S I hm ha hsigma hh hcurv
  have he:=retained_kernel_identity G S I (z:=z) (k:=k) (v:=v) (sigma:=sigma) (h:=h) hm ha hr1.ne
  have hmain' := mul_le_mul_of_nonneg_left hmain hd.le
  rw [he] at hmain'
  have hf' := mul_le_mul_of_nonneg_left hf hr
  apply (le_div_iff₀ hd).mpr
  have halg : (L+r/(1-r)*(B*h^2/2-gamma*h^4/24))*(1-r)=
      (1-r)*L+r*(B*h^2/2-gamma*h^4/24) := by field_simp
  rw [halg]
  linarith

#print axioms quadratic_shift
#print axioms shifted_curvature_lower
#print axioms negative_second_eq_kernel
#print axioms actual_finite_step
#print axioms actual_direction_lower_of_curvature
end ForestUnimodality.GaussianDirectionFiniteStep
