import ForestUnimodality.Stage80KernelData.Cell210.Budget
import ForestUnimodality.Stage170SourceData.Windows.Batch040_059
import ForestUnimodality.ActivityPointDensityData.Point105
import ForestUnimodality.ActivityPointDensityTransfer

namespace ForestUnimodality.Stage80SourceData.Cell210
open Stage80KernelData.Cell210
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def activityLower : ℚ := (53/40)
def density : ℚ := (74894391116193031996717472663/250000000000000000000000000000)
def transferFactor : ℚ := (10343104714215210038170890702418643963509/10000000000000000000000000000000000000000)

theorem activity_lower {z : ℝ} (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ)) : (activityLower:ℝ)≤z := by
  have hl := (le_div_iff₀ (by positivity : (0:ℝ)<1+z)).mp hq.1
  norm_num [interval,activityLower] at hl ⊢
  linarith

theorem actual_available_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (hS : 0<S.card) (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreAvailableVariance G S B z≤(D:ℝ)*hardCoreAvailableMean G S B z := by
  have hqw : z/(1+z)∈Set.Icc (Stage170SourceData.Window058.window.qa:ℝ) (Stage170SourceData.Window058.window.qb:ℝ) := by
    norm_num [Stage170SourceData.Window058.window,interval] at hq ⊢
    constructor <;> linarith [hq.1,hq.2]
  have hv := Stage170SourceData.Window058.window.available_variance Stage170SourceData.Window058.valid hB hG hz hS hqw hrank
  exact hv.trans (mul_le_mul_of_nonneg_right
    (show (Stage170SourceData.Window058.window.D:ℝ)≤(D:ℝ) by norm_num [Stage170SourceData.Window058.window,D])
    (hardCoreAvailableMean_nonneg G S B hz.le))

theorem density_checked :
    0<ActivityPointDensityData.Point105.certificate.parameters.x ∧ ActivityPointDensityData.Point105.certificate.parameters.x≤activityLower ∧ 0≤transferFactor ∧
    transferFactor^2*ActivityPointDensityData.Point105.certificate.parameters.x*(1+activityLower)≤activityLower*(1+ActivityPointDensityData.Point105.certificate.parameters.x) ∧
    0≤ActivityPointDensityData.Point105.certificate.parameters.h ∧
    density≤transferFactor*(ActivityPointDensityData.Point105.certificate.parameters.r+ActivityPointDensityData.Point105.certificate.parameters.h/98) := by decide +kernel

theorem actual_density (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V)
    (h8 : 8≤S.card) (hN : S.card≤98) {z : ℝ} (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ)) :
    (density:ℝ)*(S.card:ℝ)≤hardCoreMean G S z := by
  rcases density_checked with ⟨hx,hxa,hg,hfactor,hh,hrho⟩
  exact ActivityPointDensity.Certificate.finite_window_density
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point105.checked)
    (a:=(activityLower:ℝ)) (gamma:=(transferFactor:ℝ)) (rho:=(density:ℝ))
    G hG S h8 hN (by exact_mod_cast hx) (by exact_mod_cast hxa) (activity_lower hz hq)
    (by exact_mod_cast hg) (by exact_mod_cast hfactor) hh (by exact_mod_cast hrho)

#print axioms activity_lower
#print axioms actual_available_variance
#print axioms density_checked
#print axioms actual_density
end ForestUnimodality.Stage80SourceData.Cell210
