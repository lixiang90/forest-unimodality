import ForestUnimodality.Stage80KernelData.Cell048.Budget
import ForestUnimodality.MarkedAvailableWindow
import ForestUnimodality.ActivityPointDensityData.Point031
import ForestUnimodality.ActivityPointDensityTransfer

namespace ForestUnimodality.Stage80SourceData.Cell048
open Stage80KernelData.Cell048
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def activityLower : ℚ := (47/50)
def density : ℚ := (272319903519357219949881759029/1000000000000000000000000000000)
def transferFactor : ℚ := (1/1)

theorem activity_lower {z : ℝ} (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ)) : (activityLower:ℝ)≤z := by
  have hl := (le_div_iff₀ (by positivity : (0:ℝ)<1+z)).mp hq.1
  norm_num [interval,activityLower] at hl ⊢
  linarith

def availableWindow : MarkedAvailableWindow.Window := ⟨27,(47/97),(9237/19012),D⟩
theorem availableWindow_checked : availableWindow.check=true := by decide +kernel
#print axioms availableWindow_checked

theorem actual_available_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (_hS : 0<S.card) (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ))
    (_hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreAvailableVariance G S B z≤(D:ℝ)*hardCoreAvailableMean G S B z := by
  exact availableWindow.actual_available_variance availableWindow_checked hB hG hz
    (by simpa only [availableWindow,interval] using hq)

theorem density_checked :
    0<ActivityPointDensityData.Point031.certificate.parameters.x ∧ ActivityPointDensityData.Point031.certificate.parameters.x≤activityLower ∧ 0≤transferFactor ∧
    transferFactor^2*ActivityPointDensityData.Point031.certificate.parameters.x*(1+activityLower)≤activityLower*(1+ActivityPointDensityData.Point031.certificate.parameters.x) ∧
    0≤ActivityPointDensityData.Point031.certificate.parameters.h ∧
    density≤transferFactor*(ActivityPointDensityData.Point031.certificate.parameters.r+ActivityPointDensityData.Point031.certificate.parameters.h/98) := by decide +kernel

theorem actual_density (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V)
    (h8 : 8≤S.card) (hN : S.card≤98) {z : ℝ} (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ)) :
    (density:ℝ)*(S.card:ℝ)≤hardCoreMean G S z := by
  rcases density_checked with ⟨hx,hxa,hg,hfactor,hh,hrho⟩
  exact ActivityPointDensity.Certificate.finite_window_density
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point031.checked)
    (a:=(activityLower:ℝ)) (gamma:=(transferFactor:ℝ)) (rho:=(density:ℝ))
    G hG S h8 hN (by exact_mod_cast hx) (by exact_mod_cast hxa) (activity_lower hz hq)
    (by exact_mod_cast hg) (by exact_mod_cast hfactor) hh (by exact_mod_cast hrho)

#print axioms activity_lower
#print axioms actual_available_variance
#print axioms density_checked
#print axioms actual_density
end ForestUnimodality.Stage80SourceData.Cell048
