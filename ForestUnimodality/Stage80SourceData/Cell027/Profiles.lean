import ForestUnimodality.Stage80KernelData.Cell027.Budget
import ForestUnimodality.Stage170SourceData.Windows.Batch020_039
import ForestUnimodality.Stage170SourceData.Windows.Batch020_039
import ForestUnimodality.ActivityPointDensityData.Point016
import ForestUnimodality.ActivityPointDensityTransfer

/-! Actual graph profiles only. Finite kernel and Laplace bounds are separate. -/
namespace ForestUnimodality.Stage80SourceData.Cell027
open Stage80KernelData.Cell027
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def activityLower : ℚ := (301/365)
def activityUpper : ℚ := (17/20)
def density : ℚ := (130103077288361474298039803539/500000000000000000000000000000)

theorem activity_bounds {z : ℝ} (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ)) :
    (activityLower:ℝ)≤z ∧ z≤(activityUpper:ℝ) := by
  have hl := (le_div_iff₀ (by positivity : 0<1+z)).mp hq.1
  have hu := (div_le_iff₀ (by positivity : 0<1+z)).mp hq.2
  norm_num [interval,activityLower,activityUpper] at hl hu ⊢
  constructor <;> linarith

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (_hS : 0<S.card) (_hN : S.card≤98) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ)) :
    hardCoreVariance G S z≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+varianceIntercept := by
  have hqw : z/(1+z)∈Set.Icc (Stage170SourceData.Window027.window.qa:ℝ) (Stage170SourceData.Window027.window.qb:ℝ) := by
    norm_num [Stage170SourceData.Window027.window,interval] at hq ⊢
    constructor <;> linarith [hq.1,hq.2]
  have hv := Stage170SourceData.Window027.window.total_variance Stage170SourceData.Window027.valid hB hG hz hqw
  have hcoef : ((Stage170SourceData.Window027.window.R*Stage170SourceData.Window027.window.vmax:ℚ):ℝ)≤(alpha:ℝ) := by
    norm_num [Stage170SourceData.Window027.window,alpha]
  have hmul := mul_le_mul_of_nonneg_right hcoef (hardCoreAvailableMean_nonneg G S B hz.le)
  have hintercept : (0:ℝ)≤varianceIntercept := by norm_num [varianceIntercept]
  linarith

#print axioms activity_bounds
#print axioms actual_variance

theorem actual_available_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreAvailableVariance G S B z≤(D:ℝ)*hardCoreAvailableMean G S B z := by
  have hqw : z/(1+z)∈Set.Icc (Stage170SourceData.Window027.window.qa:ℝ) (Stage170SourceData.Window027.window.qb:ℝ) := by
    norm_num [Stage170SourceData.Window027.window,interval] at hq ⊢
    constructor <;> linarith [hq.1,hq.2]
  have hv := Stage170SourceData.Window027.window.available_variance Stage170SourceData.Window027.valid hB hG hz hS hqw hrank
  exact hv.trans (mul_le_mul_of_nonneg_right
    (show (Stage170SourceData.Window027.window.D:ℝ)≤(D:ℝ) by norm_num [Stage170SourceData.Window027.window,D])
    (hardCoreAvailableMean_nonneg G S B hz.le))

#print axioms actual_available_variance

def transferFactor : ℚ := (1/1)
theorem density_checked :
    0<ActivityPointDensityData.Point016.certificate.parameters.x ∧ ActivityPointDensityData.Point016.certificate.parameters.x≤activityLower ∧ 0≤transferFactor ∧
    transferFactor^2*ActivityPointDensityData.Point016.certificate.parameters.x*(1+activityLower)≤activityLower*(1+ActivityPointDensityData.Point016.certificate.parameters.x) ∧
    0≤ActivityPointDensityData.Point016.certificate.parameters.h ∧
    density≤transferFactor*(ActivityPointDensityData.Point016.certificate.parameters.r+ActivityPointDensityData.Point016.certificate.parameters.h/98) := by decide +kernel
#print axioms density_checked

theorem actual_density (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V)
    (h8 : 8≤S.card) (hN : S.card≤98) {z : ℝ} (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ))
    (_hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    (density:ℝ)*(S.card:ℝ)≤hardCoreMean G S z := by
  rcases density_checked with ⟨hx,hxa,hg,hfactor,hh,hrho⟩
  exact ActivityPointDensity.Certificate.finite_window_density
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point016.checked)
    (a:=(activityLower:ℝ)) (gamma:=(transferFactor:ℝ)) (rho:=(density:ℝ))
    G hG S h8 hN (by exact_mod_cast hx) (by exact_mod_cast hxa) (activity_bounds hz hq).1
    (by exact_mod_cast hg) (by exact_mod_cast hfactor) hh (by exact_mod_cast hrho)

#print axioms actual_density
end ForestUnimodality.Stage80SourceData.Cell027
