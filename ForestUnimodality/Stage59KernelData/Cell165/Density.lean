import ForestUnimodality.Stage59KernelData.Cell165.Parameters
import ForestUnimodality.ActivityPointDensityData.Point077
import ForestUnimodality.ActivityPointDensityTransfer

namespace ForestUnimodality.Stage59KernelData.Cell165
def density : ℚ := (288084118101209636173010121181/1000000000000000000000000000000)
def transferFactor : ℚ := 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem density_checked :
    0<ActivityPointDensityData.Point077.certificate.parameters.x ∧ ActivityPointDensityData.Point077.certificate.parameters.x≤activityLower ∧ 0≤transferFactor ∧
    transferFactor^2*ActivityPointDensityData.Point077.certificate.parameters.x*(1+activityLower)≤activityLower*(1+ActivityPointDensityData.Point077.certificate.parameters.x) ∧
    0≤ActivityPointDensityData.Point077.certificate.parameters.h ∧
    density≤transferFactor*(ActivityPointDensityData.Point077.certificate.parameters.r+ActivityPointDensityData.Point077.certificate.parameters.h/79) := by decide +kernel

theorem actual_density {V : Type*} [DecidableEq V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) (hn : 59≤S.card) (hN : S.card≤79) {z : ℝ}
    (hzlo : (activityLower:ℝ)≤z) : (density:ℝ)*(S.card:ℝ)≤hardCoreMean G S z := by
  rcases density_checked with ⟨hx,hxa,hg,hfactor,hh,hrho⟩
  exact ActivityPointDensity.Certificate.finite_window_density
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point077.checked)
    (a:=(activityLower:ℝ)) (gamma:=(transferFactor:ℝ)) (rho:=(density:ℝ))
    G hG S (by omega) hN (by exact_mod_cast hx) (by exact_mod_cast hxa) hzlo
    (by exact_mod_cast hg) (by exact_mod_cast hfactor) hh (by exact_mod_cast hrho)

#print axioms density_checked
#print axioms actual_density
end ForestUnimodality.Stage59KernelData.Cell165
