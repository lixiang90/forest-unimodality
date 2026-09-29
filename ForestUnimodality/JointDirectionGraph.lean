import ForestUnimodality.DirectionalErrorLayerBudget
import ForestUnimodality.DirectionalSmallLayerBudget
import ForestUnimodality.GaussianDirectionFiniteStep
import ForestUnimodality.PointMassLayerBudget

/-! Actual Gaussian comparison, actual shared Fourier error, and actual
small-layer gradients are assembled on one graph-layer distribution. -/
namespace ForestUnimodality.JointDirectionGraph
open Real NegativePowerLayerBudget BinomialPointMassError BinomialDirectionalError
open DirectionalErrorLayerBudget DirectionalSmallLayerBudget GaussianDirectionFiniteStep
open ShiftedLayerMoments

def orientation (reverse : Bool) : ℝ := if reverse then -1 else 1

noncomputable def normalizer (v m : ℝ) : ℝ := 1/(sqrt (2*Real.pi)*sqrt (v*m))

theorem gaussian_profile {M m v : ℝ} (hM : 0<M) (hm : 0<m) (hv : 0<v) (d : ℝ) :
    gaussianDensity (M*v) d=normalizer v m*
      GaussianFiniteStep.profile (M/m) (d/sqrt (v*m)) := by
  rw [PointMassLayerBudget.gaussianDensity_normalization hv hm hM d]
  unfold normalizer GaussianFiniteStep.profile
  rw [rpow_neg (div_pos hM hm).le,←sqrt_eq_rpow]
  ring_nf

theorem point_difference_eq (reverse : Bool) (M : ℕ) {m q : ℝ}
    (hM : 0<(M:ℝ)) (hm : 0<m) (hv : 0<q*(1-q)) (r : ℝ) (k : ℤ) :
    pointDifference reverse M q r k=signedMass reverse M q r k-
      normalizer (q*(1-q)) m*
      (GaussianFiniteStep.profile ((M:ℝ)/m) (((k:ℝ)-M*q)/sqrt ((q*(1-q))*m))-
        r*GaussianFiniteStep.profile ((M:ℝ)/m)
          ((((k:ℝ)-M*q)/sqrt ((q*(1-q))*m))+orientation reverse*(1/sqrt ((q*(1-q))*m)))) := by
  cases reverse <;> dsimp [pointDifference,signedMass,orientation]
  · rw [gaussian_profile hM hm hv,gaussian_profile hM hm hv]
    rw [show (((k:ℝ)-M*q+1)/sqrt ((q*(1-q))*m))=
      (((k:ℝ)-M*q)/sqrt ((q*(1-q))*m))+1/sqrt ((q*(1-q))*m) by ring_nf]
    ring_nf
  · rw [gaussian_profile hM hm hv,gaussian_profile hM hm hv]
    rw [show (((k:ℝ)-M*q-1)/sqrt ((q*(1-q))*m))=
      (((k:ℝ)-M*q)/sqrt ((q*(1-q))*m))-1/sqrt ((q*(1-q))*m) by ring_nf]
    ring_nf

variable {V : Type*} [DecidableEq V]

noncomputable def retainedSigned (G : SimpleGraph V) (S I : Finset V)
    (z alpha m r : ℝ) (k : ℤ) (reverse : Bool) : ℝ :=
  hardCoreLayerExpectation G S I z (fun j M=>if alpha*m≤(M:ℝ) then
    signedMass reverse M (z/(1+z)) r (k-j) else 0)

theorem averagedDifference_eq (G : SimpleGraph V) (S I : Finset V)
    {z alpha m r : ℝ} (hm : 0<m) (ha : 0<alpha)
    (hv : 0<(z/(1+z))*(1-z/(1+z))) (k : ℤ) (reverse : Bool) :
    let v:=(z/(1+z))*(1-z/(1+z))
    averagedDifference G S I z (z/(1+z)) (alpha*m) r k reverse=
      retainedSigned G S I z alpha m r k reverse-
      normalizer v m*(retainedProfile G S I z m alpha (k:ℝ) v (orientation reverse) 0-
        r*retainedProfile G S I z m alpha (k:ℝ) v (orientation reverse) (1/sqrt (v*m))) := by
  dsimp only
  unfold averagedDifference retainedSigned retainedProfile
  simp only [←layer_const_mul,←layer_sub]
  congr 1
  funext j M
  by_cases hgood : alpha*m≤(M:ℝ)
  · simp only [if_pos hgood,mul_zero,add_zero]
    rw [point_difference_eq reverse M ((mul_pos ha hm).trans_le hgood) hm hv]
    have hd : ((((k-(j:ℤ)):ℤ):ℝ)-(M:ℝ)*(z/(1+z)))=
        (k:ℝ)-binomialLayerMean j M z := by
      push_cast
      unfold binomialLayerMean
      ring_nf
    rw [hd]
    simp only [ratio,offset,add_zero]
  · simp [hgood]

theorem actual_signed_eq (G : SimpleGraph V) (S I : Finset V)
    (hIS : I⊆S) (hI : G.IsIndepSet (I:Set V)) {z : ℝ} (hz : 0<z)
    (r : ℝ) (k : ℕ) (hk : 1≤k) (reverse : Bool) :
    hardCoreLayerExpectation G S I z (fun j M=>signedMass reverse M (z/(1+z)) r ((k:ℤ)-j))=
      tiltedProbability (countIndependent G S) z (partitionFunction G S z) k-
        r*tiltedProbability (countIndependent G S) z (partitionFunction G S z)
          (if reverse then k-1 else k+1) := by
  rw [tiltedProbability_eq_binomial_mixture G S I hIS hI hz k,
    tiltedProbability_eq_binomial_mixture G S I hIS hI hz (if reverse then k-1 else k+1)]
  change hardCoreLayerExpectation G S I z _=
    hardCoreLayerExpectation G S I z _-r*hardCoreLayerExpectation G S I z _
  rw [←layer_const_mul,←layer_sub]
  congr 1
  funext j M
  unfold signedMass
  congr 2
  cases reverse <;> simp only [Bool.false_eq_true,if_false,if_true]
  · congr 1
    omega
  · congr 1
    omega

/-- A true directional probability lower bound. All random quantities in
this statement come from the same actual independent-set layer law. -/
theorem actual_direction_lower (G : SimpleGraph V) (S I : Finset V)
    (hIS : I⊆S) (hI : G.IsIndepSet (I:Set V))
    {z alpha m v eta D r L C : ℝ}
    (hz : 0<z) (hm : m=hardCoreAvailableMean G S I z) (hm0 : 0<m)
    (ha : 0<alpha) (ha1 : alpha<1) (ham : 1<alpha*m)
    (hv : 0<v) (hvq : v≤(z/(1+z))*(1-z/(1+z)))
    (hvnear : 9/40≤(z/(1+z))*(1-z/(1+z)))
    (heta : |1-2*(z/(1+z))|≤eta) (hvar : hardCoreAvailableVariance G S I z≤D*m)
    (hr : 0<r) (hr1 : r<1) (k : ℕ) (hk : 1≤k) (reverse : Bool)
    (cuts : ℕ→ℝ) (P : ℕ→ReciprocalGradientBudget.GradientProfile) (n : ℕ)
    (hstart : 0<cuts 0) (hend : cuts (n+1)=alpha*m)
    (hsteps : ∀i≤n,cuts i≤cuts (i+1))
    (hP : ∀i≤n,(P i).Valid (z/(1+z)) v (cuts i))
    (hbad : hardCoreLayerExpectation G S I z (fun _ M=>badCost v cuts P n M)≤C)
    (hGaussian :
      let vq:=(z/(1+z))*(1-z/(1+z))
      L≤(retainedProfile G S I z m alpha (k:ℝ) vq (orientation reverse) 0-
        r*retainedProfile G S I z m alpha (k:ℝ) vq (orientation reverse) (1/sqrt (vq*m)))/(1-r)) :
    normalizer ((z/(1+z))*(1-z/(1+z))) m*(1-r)*L-
      sqrt (zeroBudget alpha m v eta D*((1-r)^2*zeroBudget alpha m v eta D+
        r*twoBudget alpha m v eta D))-r*C≤
      tiltedProbability (countIndependent G S) z (partitionFunction G S z) k-
        r*tiltedProbability (countIndependent G S) z (partitionFunction G S z)
          (if reverse then k-1 else k+1) := by
  have hvq0:=hv.trans_le hvq
  have he:=actual_averaged_error_explicit G S I hIS hI hz.le hm hm0 ha ha1 ham hv hvq hvnear
    heta hvar hr (k:ℤ) reverse
  rw [averagedDifference_eq G S I hm0 ha hvq0] at he
  have herr:=(abs_le.mp he).1
  simp only [Int.cast_natCast] at herr
  have hq0 : 0≤z/(1+z) := by positivity
  have hq1 : z/(1+z)≤1 := (div_le_one (by positivity)).mpr (by linarith)
  have hwhole:=whole_direction_ge_retained G S I hz.le hq0 hq1 hv hr.le hr1.le cuts P n
    hstart hsteps hP reverse (k:ℤ)
  rw [hend,actual_signed_eq G S I hIS hI hz r k hk reverse] at hwhole
  have hbad':=mul_le_mul_of_nonneg_left hbad hr.le
  have hd : 0<1-r := sub_pos.mpr hr1
  have hc : 0<normalizer ((z/(1+z))*(1-z/(1+z))) m := by
    unfold normalizer
    positivity
  have hg:=mul_le_mul_of_nonneg_left ((le_div_iff₀ hd).mp hGaussian) hc.le
  change retainedSigned G S I z alpha m r (k:ℤ) reverse-
    r*hardCoreLayerExpectation G S I z (fun _ M=>badCost v cuts P n M)≤_ at hwhole
  nlinarith

#print axioms averagedDifference_eq
#print axioms actual_signed_eq
#print axioms actual_direction_lower
end ForestUnimodality.JointDirectionGraph
