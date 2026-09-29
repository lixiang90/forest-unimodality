import ForestUnimodality.Stage80KernelData.Cell216.Budget
import ForestUnimodality.Stage80ConstantLibrary
import ForestUnimodality.LogVarianceProfile
import ForestUnimodality.Stage170SourceData.Windows.Batch060_079
import ForestUnimodality.ActivityPointDensityData.Point105
import ForestUnimodality.ActivityPointDensityTransfer

/-! Actual graph profiles only. Finite kernel and Laplace bounds are separate. -/
namespace ForestUnimodality.Stage80SourceData.Cell216
open Stage80KernelData.Cell216
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def activityLower : ℚ := (653/475)
def activityUpper : ℚ := (7/5)
def density : ℚ := (150967989114911869865583961491/500000000000000000000000000000)

theorem activity_bounds {z : ℝ} (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ)) :
    (activityLower:ℝ)≤z ∧ z≤(activityUpper:ℝ) := by
  have hl := (le_div_iff₀ (by positivity : 0<1+z)).mp hq.1
  have hu := (div_le_iff₀ (by positivity : 0<1+z)).mp hq.2
  norm_num [interval,activityLower,activityUpper] at hl hu ⊢
  constructor <;> linarith

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (_hS : 0<S.card) (hN : S.card≤98) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ)) :
    hardCoreVariance G S z≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+varianceIntercept := by
  have hab := activity_bounds hz hq
  have hlo : (Stage80ConstantData.Case34.domain.lower:ℝ)≤z := by
    norm_num [Stage80ConstantLibrary.domain, Stage80ConstantLibrary.parameters, Stage80ConstantLibrary.factor, Stage80ConstantData.Case34.parameters, Stage80ConstantData.Case34.domain,activityLower] at hab ⊢
    linarith
  have hhi : z≤(Stage80ConstantData.Case34.domain.b:ℝ) := by
    norm_num [Stage80ConstantLibrary.domain, Stage80ConstantLibrary.parameters, Stage80ConstantLibrary.factor, Stage80ConstantData.Case34.parameters, Stage80ConstantData.Case34.domain,activityUpper] at hab ⊢
    linarith
  have hv := Stage80ConstantLibrary.actual_variance_le_mass 11 hB hG hlo hhi
  have hfactor : Stage80ConstantLibrary.factor 11=((8693969/10000000):ℚ) := by decide +kernel
  rw [hfactor] at hv
  rw [hardCoreOccupiedMass_eq_activity_available_mean G S B hB.subset hB.independent hz] at hv
  have hlin : hardCoreVariance G S z≤((8693969/10000000):ℝ)*
      (z/(1+z)*hardCoreAvailableMean G S B z)+((0/1):ℝ)*(S.card:ℝ) := by
    norm_num [Stage80ConstantLibrary.domain, Stage80ConstantLibrary.parameters, Stage80ConstantLibrary.factor, Stage80ConstantData.Case34.parameters, Stage80ConstantData.Case34.domain] at hv ⊢
    exact hv
  have hcoef := quadratic_profile_of_endpoints (C:=((8693969/10000000):ℝ)) hq
    (show ((8693969/10000000):ℝ)*(interval.lo:ℝ)-(interval.lo:ℝ)*(1-interval.lo)≤(alpha:ℝ) by norm_num [alpha,interval])
    (show ((8693969/10000000):ℝ)*(interval.hi:ℝ)-(interval.hi:ℝ)*(1-interval.hi)≤(alpha:ℝ) by norm_num [alpha,interval])
  have hm := mul_le_mul_of_nonneg_right hcoef (hardCoreAvailableMean_nonneg G S B hz.le)
  have hnR : (S.card:ℝ)≤98 := by exact_mod_cast hN
  have hintercept : ((0/1):ℝ)*(S.card:ℝ)≤(varianceIntercept:ℝ) :=
    (mul_le_mul_of_nonneg_left hnR (by norm_num)).trans (by norm_num [varianceIntercept])
  nlinarith

#print axioms activity_bounds
#print axioms actual_variance

theorem actual_available_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreAvailableVariance G S B z≤(D:ℝ)*hardCoreAvailableMean G S B z := by
  have hqw : z/(1+z)∈Set.Icc (Stage170SourceData.Window061.window.qa:ℝ) (Stage170SourceData.Window061.window.qb:ℝ) := by
    norm_num [Stage170SourceData.Window061.window,interval] at hq ⊢
    constructor <;> linarith [hq.1,hq.2]
  have hv := Stage170SourceData.Window061.window.available_variance Stage170SourceData.Window061.valid hB hG hz hS hqw hrank
  exact hv.trans (mul_le_mul_of_nonneg_right
    (show (Stage170SourceData.Window061.window.D:ℝ)≤(D:ℝ) by norm_num [Stage170SourceData.Window061.window,D])
    (hardCoreAvailableMean_nonneg G S B hz.le))

#print axioms actual_available_variance

def transferFactor : ℚ := (2084906087943915423165794400601347654231/2000000000000000000000000000000000000000)
theorem density_checked :
    0<ActivityPointDensityData.Point105.certificate.parameters.x ∧ ActivityPointDensityData.Point105.certificate.parameters.x≤activityLower ∧ 0≤transferFactor ∧
    transferFactor^2*ActivityPointDensityData.Point105.certificate.parameters.x*(1+activityLower)≤activityLower*(1+ActivityPointDensityData.Point105.certificate.parameters.x) ∧
    0≤ActivityPointDensityData.Point105.certificate.parameters.h ∧
    density≤transferFactor*(ActivityPointDensityData.Point105.certificate.parameters.r+ActivityPointDensityData.Point105.certificate.parameters.h/98) := by decide +kernel
#print axioms density_checked

theorem actual_density (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V)
    (h8 : 8≤S.card) (hN : S.card≤98) {z : ℝ} (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ))
    (_hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    (density:ℝ)*(S.card:ℝ)≤hardCoreMean G S z := by
  rcases density_checked with ⟨hx,hxa,hg,hfactor,hh,hrho⟩
  exact ActivityPointDensity.Certificate.finite_window_density
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point105.checked)
    (a:=(activityLower:ℝ)) (gamma:=(transferFactor:ℝ)) (rho:=(density:ℝ))
    G hG S h8 hN (by exact_mod_cast hx) (by exact_mod_cast hxa) (activity_bounds hz hq).1
    (by exact_mod_cast hg) (by exact_mod_cast hfactor) hh (by exact_mod_cast hrho)

#print axioms actual_density
end ForestUnimodality.Stage80SourceData.Cell216
