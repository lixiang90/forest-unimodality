import ForestUnimodality.Stage59KernelData.Cell164.Parameters
import ForestUnimodality.ActivityPointDensityData.Point076
import ForestUnimodality.ActivityPointDensityTransfer

namespace ForestUnimodality.Stage59KernelData.Cell164
def density : ℚ := (143942669314310070142394095669/500000000000000000000000000000)
def transferFactor : ℚ := 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem density_checked :
    0<ActivityPointDensityData.Point076.certificate.parameters.x ∧ ActivityPointDensityData.Point076.certificate.parameters.x≤activityLower ∧ 0≤transferFactor ∧
    transferFactor^2*ActivityPointDensityData.Point076.certificate.parameters.x*(1+activityLower)≤activityLower*(1+ActivityPointDensityData.Point076.certificate.parameters.x) ∧
    0≤ActivityPointDensityData.Point076.certificate.parameters.h ∧
    density≤transferFactor*(ActivityPointDensityData.Point076.certificate.parameters.r+ActivityPointDensityData.Point076.certificate.parameters.h/79) := by decide +kernel

theorem actual_density {V : Type*} [DecidableEq V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) (hn : 59≤S.card) (hN : S.card≤79) {z : ℝ}
    (hzlo : (activityLower:ℝ)≤z) : (density:ℝ)*(S.card:ℝ)≤hardCoreMean G S z := by
  rcases density_checked with ⟨hx,hxa,hg,hfactor,hh,hrho⟩
  exact ActivityPointDensity.Certificate.finite_window_density
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point076.checked)
    (a:=(activityLower:ℝ)) (gamma:=(transferFactor:ℝ)) (rho:=(density:ℝ))
    G hG S (by omega) hN (by exact_mod_cast hx) (by exact_mod_cast hxa) hzlo
    (by exact_mod_cast hg) (by exact_mod_cast hfactor) hh (by exact_mod_cast hrho)

#print axioms density_checked
#print axioms actual_density
end ForestUnimodality.Stage59KernelData.Cell164
