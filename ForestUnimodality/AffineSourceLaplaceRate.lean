import ForestUnimodality.AffineSourceLibrary
import ForestUnimodality.AffineTailRateCertificate
import ForestUnimodality.MeanMatchedSourceBudget

/-! Whole-interval Laplace pricing from the actual affine source and a fixed
maximum-marginal independent set. Rational retention need only be below the
certified exponential retention, which avoids assuming a logarithm evaluation. -/
namespace ForestUnimodality
open Finset Set
variable {V : Type*} [DecidableEq V]

theorem hardCoreLayerLaplace_mono (G : SimpleGraph V) (S B : Finset V)
    {z t u : ℝ} (hz : 0≤z) (ht : 0≤t) (htu : t≤u) :
    hardCoreLayerLaplace G S B z t≤hardCoreLayerLaplace G S B z u := by
  have hq : 0≤z/(1+z) := by positivity
  have hq1 : z/(1+z)≤1 := (div_le_one (by positivity)).mpr (by linarith)
  have hbase : 0≤1-z/(1+z)+z/(1+z)*t := by positivity
  have hbasele : 1-z/(1+z)+z/(1+z)*t≤1-z/(1+z)+z/(1+z)*u := by
    nlinarith [mul_le_mul_of_nonneg_left htu hq]
  unfold hardCoreLayerLaplace hardCoreLayerExpectation
  apply sum_le_sum
  intro j _
  apply sum_le_sum
  intro m _
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase hbasele m)
    (hardCoreLayerWeight_nonneg G S B hz j m)

theorem IsMaximumMarginalIndependentOn.laplace_le_affine_source_rate
    {G : SimpleGraph V} {S B : Finset V} {z ρ u rate lo hi : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (i : Fin 15) (hz : 0<z) (hzb : z≤((AffineSourceLibrary.domain i).b:ℝ))
    (hρ : 0<ρ) (hρq : ρ≤z/(1+z)) (hu : 0≤u)
    (hdensity : ρ*(S.card:ℝ)≤hardCoreMean G S z)
    (hlo : 0≤lo) (hhi : hi≤1) (hq : z/(1+z)∈Icc lo hi)
    (hrlo : rate≤AffineLaplace.tailRate (AffineSourceLibrary.parameters i).A
      (AffineSourceLibrary.parameters i).C ρ 0 u lo)
    (hrhi : rate≤AffineLaplace.tailRate (AffineSourceLibrary.parameters i).A
      (AffineSourceLibrary.parameters i).C ρ 0 u hi) :
    hardCoreLayerLaplace G S B z (Real.exp (-u))≤
      Real.exp (-rate*hardCoreAvailableMean G S B z) := by
  have hP := AffineSource.Parameters.check_sound (AffineSourceLibrary.parameters_checked i)
  have hC := AffineSourceLibrary.C_pos i
  have h := hardCoreLayerLaplace_le_exp_affine G S B hB.subset hB.independent hz hu hC
    (fun t ht=>AffineSourceLibrary.actual_tilt i G hG S B hB.subset hz hzb t ht.1)
  have hcard := hB.card_le_available_of_density hG hz hρ hρq hdensity
  have hcoef : 0≤((AffineSourceLibrary.parameters i).A:ℝ)/(AffineSourceLibrary.parameters i).C*
      (u-AffineLaplace.decayIntegral (AffineSourceLibrary.parameters i).C u) :=
    mul_nonneg (div_nonneg hP.2.1 hC.le)
      (sub_nonneg.mpr (AffineLaplace.decayIntegral_le hC hu))
  have hsize := mul_le_mul_of_nonneg_left hcard hcoef
  have hm := hardCoreOccupiedMass_eq_activity_available_mean G S B hB.subset hB.independent hz
  have hrate := AffineLaplace.tailRate_lower_of_endpoints
    ((AffineSourceLibrary.parameters i).A:ℝ) ((AffineSourceLibrary.parameters i).C:ℝ) ρ
    (by norm_num : (0:ℝ)≤0) hu hlo hhi (hq.1.trans hq.2) hrlo hrhi hq
  have hrate' := mul_le_mul_of_nonneg_right hrate (hardCoreAvailableMean_nonneg G S B hz.le)
  apply h.trans
  apply Real.exp_le_exp.mpr
  rw [hm]
  unfold AffineLaplace.tailRate at hrate'
  simp only [zero_mul,add_zero,div_eq_mul_inv] at hsize hrate' ⊢
  nlinarith

namespace AffineSourceLaplaceRate

theorem actual_laplace_of_certificates (i : Fin 15)
    (wlo whi : AffineTailRateCertificate.Certificate)
    {ρ u qa qb retention rate : ℚ}
    (hlo : wlo.check (AffineSourceLibrary.parameters i).A (AffineSourceLibrary.parameters i).C
      ρ 0 u qa rate=true)
    (hhi : whi.check (AffineSourceLibrary.parameters i).A (AffineSourceLibrary.parameters i).C
      ρ 0 u qb rate=true)
    (ht : 0≤retention) (hte : retention≤wlo.uLower) (hqa : 0≤qa) (hqb : qb≤1)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hzb : z≤((AffineSourceLibrary.domain i).b:ℝ))
    (hS : 0<S.card) (hq : z/(1+z)∈Icc (qa:ℝ) (qb:ℝ))
    (hdensity : (ρ:ℝ)*(S.card:ℝ)≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hw : wlo.Accepts (AffineSourceLibrary.parameters i).A (AffineSourceLibrary.parameters i).C
      ρ 0 u qa rate := of_decide_eq_true hlo
  have hρ : (0:ℝ)<ρ := by exact_mod_cast hw.2.2.1
  have hu : (0:ℝ)≤u := by exact_mod_cast hw.2.2.2.2.1
  have he := (wlo.expU.check_sound hw.2.2.2.2.2.2.2.1).1
  have ht' : (retention:ℝ)≤Real.exp (-(u:ℝ)) := by
    have hh : (retention:ℝ)≤wlo.uLower := by exact_mod_cast hte
    exact hh.trans (by simpa using he)
  apply (hardCoreLayerLaplace_mono G S B hz.le (by exact_mod_cast ht) ht').trans
  exact hB.laplace_le_affine_source_rate hG i hz hzb hρ
    (MeanMatchedSourceBudget.density_le_probability_cap G S hz hS hdensity)
    hu hdensity (by exact_mod_cast hqa) (by exact_mod_cast hqb) hq
    (by simpa only [Rat.cast_zero] using wlo.check_sound hlo)
    (by simpa only [Rat.cast_zero] using whi.check_sound hhi)

#print axioms actual_laplace_of_certificates
end AffineSourceLaplaceRate
#print axioms hardCoreLayerLaplace_mono
#print axioms IsMaximumMarginalIndependentOn.laplace_le_affine_source_rate
end ForestUnimodality
