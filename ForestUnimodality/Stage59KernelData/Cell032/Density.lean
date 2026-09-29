import ForestUnimodality.Stage59KernelData.Cell032.Parameters
import ForestUnimodality.ActivityPointDensityData.Point019
import ForestUnimodality.ActivityPointDensityTransfer

namespace ForestUnimodality.Stage59KernelData.Cell032
def density : ℚ := (66648255801580204885740793509/250000000000000000000000000000)
def transferFactor : ℚ := 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem density_checked :
    0<ActivityPointDensityData.Point019.certificate.parameters.x ∧ ActivityPointDensityData.Point019.certificate.parameters.x≤activityLower ∧ 0≤transferFactor ∧
    transferFactor^2*ActivityPointDensityData.Point019.certificate.parameters.x*(1+activityLower)≤activityLower*(1+ActivityPointDensityData.Point019.certificate.parameters.x) ∧
    0≤ActivityPointDensityData.Point019.certificate.parameters.h ∧
    density≤transferFactor*(ActivityPointDensityData.Point019.certificate.parameters.r+ActivityPointDensityData.Point019.certificate.parameters.h/79) := by decide +kernel

theorem actual_density {V : Type*} [DecidableEq V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) (hn : 59≤S.card) (hN : S.card≤79) {z : ℝ}
    (hzlo : (activityLower:ℝ)≤z) : (density:ℝ)*(S.card:ℝ)≤hardCoreMean G S z := by
  rcases density_checked with ⟨hx,hxa,hg,hfactor,hh,hrho⟩
  exact ActivityPointDensity.Certificate.finite_window_density
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point019.checked)
    (a:=(activityLower:ℝ)) (gamma:=(transferFactor:ℝ)) (rho:=(density:ℝ))
    G hG S (by omega) hN (by exact_mod_cast hx) (by exact_mod_cast hxa) hzlo
    (by exact_mod_cast hg) (by exact_mod_cast hfactor) hh (by exact_mod_cast hrho)

#print axioms density_checked
#print axioms actual_density
end ForestUnimodality.Stage59KernelData.Cell032
