import ForestUnimodality.SignedGaussianSlices
import ForestUnimodality.ShiftedLayerMoments

/-! The shifted Gaussian is averaged under the original hard-core law.
The shift changes neither the available-count random variable nor the
exponent in its certified lower-tail bounds. -/
namespace ForestUnimodality.SignedGaussianShiftedLayerBudget
open Finset Real SignedGaussianProfile SignedGaussianHermite NegativePowerLayerBudget
open ShiftedLayerMoments
variable {V : Type*} [DecidableEq V]

theorem shifted_slice_eq (G : SimpleGraph V) (S I : Finset V) (z : ℝ)
    {m c lo hi : ℝ} (hm : 0<m) (hc : 0≤c) :
    hardCoreLayerExpectation G S I z (fun _ M=>
      if lo≤ratio m c M ∧ ratio m c M<hi then 1 else 0)=
      hardCoreAvailableSlice G S I z (lo*(m+c)-c) (hi*(m+c)-c) := by
  have hmc : 0<m+c := by linarith
  have he (M : ℕ) : (lo≤ratio m c M ∧ ratio m c M<hi) ↔
      lo*(m+c)-c≤(M:ℝ) ∧ (M:ℝ)<hi*(m+c)-c := by
    unfold ratio
    rw [le_div_iff₀ hmc,div_lt_iff₀ hmc]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  unfold hardCoreAvailableSlice
  simp only [he]

theorem shifted_tail_le_original (G : SimpleGraph V) (S I : Finset V)
    {z m c t : ℝ} (hz : 0≤z) (hm : 0<m) (hc : 0≤c) (ht : t≤1) :
    hardCoreAvailableLowerTail G S I z (t*(m+c)-c)≤
      hardCoreAvailableLowerTail G S I z (t*m) := by
  have hmc : 0<m+c := by linarith
  have he (M : ℕ) : (M:ℝ)<t*(m+c)-c ↔ ratio m c M<t := by
    unfold ratio
    rw [div_lt_iff₀ hmc]
    constructor <;> intro h <;> linarith
  simpa only [hardCoreAvailableLowerTail,he] using
    lowerTail_le_original G S I hz hm hc ht

theorem slice_cost_le (G : SimpleGraph V) (S I : Finset V)
    {z m c beta : ℝ} (hz : 0≤z) (hm : 0<m) (hc : 0≤c) (hb1 : beta≤1)
    (cuts U rate : ℕ→ℝ) (n : ℕ) (hend : cuts (n+1)=beta)
    (hsteps : ∀i≤n,cuts i≤cuts (i+1)) (hUn : ∀i≤n,0≤U i)
    (hUdec : ∀i<n,U (i+1)≤U i) (hUlast : U (n+1)=0)
    (htail : ∀i≤n,hardCoreAvailableLowerTail G S I z (cuts (i+1)*m)≤exp (-m*rate i)) :
    hardCoreLayerExpectation G S I z (fun _ M=>
      ∑i∈range (n+1),U i*(if cuts i≤ratio m c M ∧ ratio m c M<cuts (i+1) then 1 else 0))≤
      ∑i∈range (n+1),(U i-U (i+1))*exp (-m*rate i) := by
  have hmc : 0≤m+c := by linarith
  simp only [layer_sum,layer_const_mul,shifted_slice_eq G S I z hm hc]
  have hb (i : ℕ) (hi : i≤n) : cuts (i+1)≤1 := by
    have ht:=cut_le_of_steps cuts n hsteps (i:=i+1) (j:=n+1) (by omega) le_rfl
    rw [hend] at ht
    exact ht.trans hb1
  have ht (i : ℕ) (hi : i≤n) :=
    (shifted_tail_le_original G S I hz hm hc (hb i hi)).trans (htail i hi)
  have hh:=hardCoreAvailableSlices_le_cumulative G S I hz
    (fun i=>cuts i*(m+c)-c) U (fun i=>exp (-m*rate (i-1))) n
    (fun i hi=>sub_le_sub_right (mul_le_mul_of_nonneg_right (hsteps i hi) hmc) c)
    (hUn 0 (Nat.zero_le n)) (hUn n le_rfl) hUdec (fun i hi=>by simpa using ht i hi)
  simp only [Nat.add_sub_cancel] at hh
  have he : U n*exp (-m*rate n)+∑i∈range n,(U i-U (i+1))*exp (-m*rate i)=
      ∑i∈range (n+1),(U i-U (i+1))*exp (-m*rate i) := by
    rw [sum_range_succ,hUlast,sub_zero]
    ring
  exact hh.trans_eq he

/-- The signed main term with arbitrary deterministic nonnegative shift.
The only tail hypotheses concern the actual unshifted free count. -/
theorem actual_normalized_lower (G : SimpleGraph V) (S I : Finset V)
    (hIS : I⊆S) (hI : G.IsIndepSet (I:Set V))
    {z m c cmax k v R D gamma K alpha beta : ℝ}
    (hz : 0<z) (hm : m=hardCoreAvailableMean G S I z) (hm0 : 0<m)
    (hc : 0≤c) (hcc : c≤cmax) (hmean : hardCoreMean G S z=k) (hv : 0<v)
    (hR : 0≤R) (hD : 0≤D) (hg : 0<gamma) (hg3 : gamma<3)
    (ha : 0<alpha) (hab : alpha<beta) (hb1 : beta≤1)
    (hK : K≤coefficient gamma beta) (hKn : K≤0) (hL : 0≤first gamma 1)
    (hbad : profile gamma 1+first gamma 1*((alpha*m+cmax)/(m+cmax)-1)+
      K*((alpha*m+cmax)/(m+cmax)-1)^2≤0)
    (hvarL : hardCoreVariance G S z-(z/(1+z))*(1-z/(1+z))*m≤R*(v*m))
    (hvarM : hardCoreAvailableVariance G S I z≤D*m)
    (cuts U rate : ℕ→ℝ) (n : ℕ) (hstart : cuts 0=alpha) (hend : cuts (n+1)=beta)
    (hsteps : ∀i≤n,cuts i≤cuts (i+1))
    (hU : ∀i≤n,positiveGap gamma K (cuts i)≤U i)
    (hUdec : ∀i<n,U (i+1)≤U i) (hUlast : U (n+1)=0)
    (htail : ∀i≤n,hardCoreAvailableLowerTail G S I z (cuts (i+1)*m)≤exp (-m*rate i)) :
    profile gamma 1-(gamma/2)*R+K*D/m-
      (∑i∈range (n+1),(U i-U (i+1))*exp (-m*rate i))≤
    hardCoreLayerExpectation G S I z (fun j M=>if alpha*m≤(M:ℝ) then
      SignedGaussianLayerBudget.kernel (ratio m c M) (offset z m c k v j M) else 0) := by
  have ha1 : alpha≤1 := hab.le.trans hb1
  have hUn (i : ℕ) (hi : i≤n) : 0≤U i := (le_max_left _ _).trans (hU i hi)
  have he (y w : ℝ) : SignedGaussianSlices.envelope gamma K y w=
      ShiftedLayerMoments.quadratic (profile gamma 1) (first gamma 1) (gamma/2) (-K) y w := by
    unfold SignedGaussianSlices.envelope SignedGaussianHermite.quadratic ShiftedLayerMoments.quadratic
    ring
  have hpoint (j M : ℕ) :
      ShiftedLayerMoments.quadratic (profile gamma 1) (first gamma 1) (gamma/2) (-K)
        (ratio m c M) (offset z m c k v j M)-
        (∑i∈range (n+1),U i*(if cuts i≤ratio m c M ∧ ratio m c M<cuts (i+1) then 1 else 0))≤
      if alpha*m≤(M:ℝ) then
        SignedGaussianLayerBudget.kernel (ratio m c M) (offset z m c k v j M) else 0 := by
    by_cases hM : alpha*m≤(M:ℝ)
    · rw [if_pos hM,←he]
      exact SignedGaussianSlices.lower_with_slices hg hg3 ha hab hb1 hK cuts U n
        hstart hend hsteps hU (ratio_good hm0 hc ha1 hM) _
    · rw [if_neg hM]
      have ht : (alpha*m+cmax)/(m+cmax)≤1 := by
        apply (div_le_iff₀ (by linarith : 0<m+cmax)).mpr
        nlinarith
      have hq:=quadratic_nonpos_below (w:=offset z m c k v j M) hL (show 0≤gamma/2 by positivity) (neg_nonneg.mpr hKn) ht
        (ratio_bad_upper hm0 hc hcc ha1 (lt_of_not_ge hM)) (by simpa using hbad)
      have hs : 0≤∑i∈range (n+1),U i*
          (if cuts i≤ratio m c M ∧ ratio m c M<cuts (i+1) then 1 else 0) := by
        apply sum_nonneg
        intro i hi
        exact mul_nonneg (hUn i (by have:=mem_range.mp hi; omega)) (by split_ifs <;> norm_num)
      linarith
  have hp:=layer_mono G S I hz.le _ _ hpoint
  rw [layer_sub] at hp
  have hq:=quadratic_expectation_lower G S I hIS hI hz hm hm0 hc hmean hv
    (show 0≤gamma/2 by positivity) (neg_nonneg.mpr hKn) hR hD hvarL hvarM
      (H:=profile gamma 1) (L:=first gamma 1)
  have hs:=slice_cost_le G S I hz.le hm0 hc hb1 cuts U rate n hend hsteps hUn hUdec hUlast htail
  simp only [neg_mul,neg_div,sub_neg_eq_add] at hq
  linarith

theorem retained_kernel_eq_scaled_curvature (G : SimpleGraph V) (S I : Finset V)
    {z m c k v alpha : ℝ} (hm : 0<m) (hc : 0≤c) (hv : 0<v) (ha : 0<alpha) :
    hardCoreLayerExpectation G S I z (fun j M=>if alpha*m≤(M:ℝ) then
      SignedGaussianLayerBudget.kernel (ratio m c M) (offset z m c k v j M) else 0)=
    (sqrt (2*Real.pi)*(v*(m+c))*sqrt (v*(m+c))) *
      hardCoreLayerExpectation G S I z (fun j M=>if alpha*m≤(M:ℝ) then
        GaussianCurvatureFourier.curvature (v*((M:ℝ)+c)) (k-binomialLayerMean j M z) else 0) := by
  have hmc : 0<m+c := by linarith
  have he (j M : ℕ) : (if alpha*m≤(M:ℝ) then
      SignedGaussianLayerBudget.kernel (ratio m c M) (offset z m c k v j M) else 0)=
      (sqrt (2*Real.pi)*(v*(m+c))*sqrt (v*(m+c))) *
      (if alpha*m≤(M:ℝ) then
        GaussianCurvatureFourier.curvature (v*((M:ℝ)+c)) (k-binomialLayerMean j M z) else 0) := by
    by_cases hM : alpha*m≤(M:ℝ)
    · rw [if_pos hM,if_pos hM]
      have hM0 : 0<(M:ℝ)+c := by have := (mul_pos ha hm).trans_le hM; linarith
      unfold ratio offset
      have hr : ((M:ℝ)+c)/(m+c)=(v*((M:ℝ)+c))/(v*(m+c)) := by field_simp
      rw [hr,SignedGaussianLayerBudget.kernel_eq_scaled_curvature (mul_pos hv hmc) (mul_pos hv hM0)]
    · simp only [if_neg hM,mul_zero]
  simp_rw [he]
  exact layer_const_mul _ _ _ _ _ _

/-- The deterministic triangular-noise shift is exactly 1/6 in physical
variance, while the same original cutoff alpha*m is retained. -/
theorem retained_kernel_eq_lattice_curvature (G : SimpleGraph V) (S I : Finset V)
    {z m k v alpha : ℝ} (hm : 0<m) (hv : 0<v) (ha : 0<alpha) :
    hardCoreLayerExpectation G S I z (fun j M=>if alpha*m≤(M:ℝ) then
      SignedGaussianLayerBudget.kernel (ratio m (1/(6*v)) M)
        (offset z m (1/(6*v)) k v j M) else 0)=
    (sqrt (2*Real.pi)*(v*m+1/6)*sqrt (v*m+1/6)) *
      hardCoreLayerExpectation G S I z (fun j M=>if alpha*m≤(M:ℝ) then
        GaussianCurvatureFourier.curvature (v*M+1/6) (k-binomialLayerMean j M z) else 0) := by
  have he (x : ℝ) : v*(x+1/(6*v))=v*x+1/6 := by field_simp
  simpa only [he] using retained_kernel_eq_scaled_curvature G S I hm (by positivity : 0≤1/(6*v)) hv ha

/-- Restoring the original physical normalization only loses the explicit
positive shift factor. The sign premise concerns the computed main budget. -/
theorem original_scale_lower {m c cmax v B E : ℝ}
    (hm : 0<m) (hc : 0≤c) (hcc : c≤cmax) (hv : 0<v) (hB : 0≤B)
    (hbound : B≤(sqrt (2*Real.pi)*(v*(m+c))*sqrt (v*(m+c)))*E) :
    (m*sqrt m/((m+cmax)*sqrt (m+cmax)))*B≤
      (sqrt (2*Real.pi)*(v*m)*sqrt (v*m))*E := by
  have hmc : 0<m+c := by linarith
  have hmx : 0<m+cmax := by linarith
  have hsc : 0<sqrt (2*Real.pi)*(v*(m+c))*sqrt (v*(m+c)) := by positivity
  have he0 : 0≤E := by nlinarith
  have hsx : 0≤(m+c)*sqrt (m+c) := by positivity
  have hden : (m+c)*sqrt (m+c)≤(m+cmax)*sqrt (m+cmax) :=
    mul_le_mul (by linarith) (sqrt_le_sqrt (by linarith)) (sqrt_nonneg _) hmx.le
  have hratio : m*sqrt m/((m+cmax)*sqrt (m+cmax))≤m*sqrt m/((m+c)*sqrt (m+c)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  have heq : (m*sqrt m/((m+c)*sqrt (m+c))) *
      (sqrt (2*Real.pi)*(v*(m+c))*sqrt (v*(m+c)))=
      sqrt (2*Real.pi)*(v*m)*sqrt (v*m) := by
    rw [sqrt_mul hv.le,sqrt_mul hv.le]
    field_simp
  calc
    _≤(m*sqrt m/((m+c)*sqrt (m+c)))*B := mul_le_mul_of_nonneg_right hratio hB
    _≤(m*sqrt m/((m+c)*sqrt (m+c)))*
        ((sqrt (2*Real.pi)*(v*(m+c))*sqrt (v*(m+c)))*E) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _=_ := by rw [←mul_assoc,heq]

#print axioms shifted_tail_le_original
#print axioms slice_cost_le
#print axioms actual_normalized_lower
#print axioms retained_kernel_eq_lattice_curvature
#print axioms original_scale_lower
end ForestUnimodality.SignedGaussianShiftedLayerBudget
