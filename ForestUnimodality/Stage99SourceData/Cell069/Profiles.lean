import ForestUnimodality.Stage99KernelData.Cell069.Budget
import ForestUnimodality.Stage80MessageSourceData.Case041.Actual
import ForestUnimodality.LogVarianceProfile
import ForestUnimodality.MarkedAvailableWindow
import ForestUnimodality.ActivityPointDensityData.Point047
import ForestUnimodality.ActivityPointDensityTransfer

/-! Actual graph profiles only. Finite kernel and Laplace bounds are separate. -/
namespace ForestUnimodality.Stage99SourceData.Cell069
open Stage99KernelData.Cell069
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def activityLower : ℚ := (51/50)
def activityUpper : ℚ := (10429/10175)
def density : ℚ := (278942025352290208407290938451/1000000000000000000000000000000)

theorem activity_bounds {z : ℝ} (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ)) :
    (activityLower:ℝ)≤z ∧ z≤(activityUpper:ℝ) := by
  have hl := (le_div_iff₀ (by positivity : 0<1+z)).mp hq.1
  have hu := (div_le_iff₀ (by positivity : 0<1+z)).mp hq.2
  norm_num [interval,activityLower,activityUpper] at hl hu ⊢
  constructor <;> linarith

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hS : 0<S.card) (hN : S.card≤129) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ)) :
    hardCoreVariance G S z≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+varianceIntercept := by
  have hab := activity_bounds hz hq
  have hlo : (Stage80MessageSourceData.Case041.parameters.lower:ℝ)≤z := by
    norm_num [Stage80MessageSourceData.Case041.parameters, Stage80MessagePriceData.case041, MessagePriceSpline.Parameters.toReal,activityLower] at hab ⊢
    linarith
  have hhi : z≤(Stage80MessageSourceData.Case041.parameters.upper:ℝ) := by
    norm_num [Stage80MessageSourceData.Case041.parameters, Stage80MessagePriceData.case041, MessagePriceSpline.Parameters.toReal,activityUpper] at hab ⊢
    linarith
  have hv := Stage80MessageSourceData.Case041.actual_variance_le_mass hB hG (Finset.card_pos.mp hS) hlo hhi
  rw [hardCoreOccupiedMass_eq_activity_available_mean G S B hB.subset hB.independent hz] at hv
  have hlin : hardCoreVariance G S z≤((41719438469/50000000000):ℝ)*
      (z/(1+z)*hardCoreAvailableMean G S B z)+((0/1):ℝ)*(S.card:ℝ) := by
    norm_num [Stage80MessageSourceData.Case041.parameters, Stage80MessagePriceData.case041, MessagePriceSpline.Parameters.toReal] at hv ⊢
    exact hv
  have hcoef := quadratic_profile_of_endpoints (C:=((41719438469/50000000000):ℝ)) hq
    (show ((41719438469/50000000000):ℝ)*(interval.lo:ℝ)-(interval.lo:ℝ)*(1-interval.lo)≤(alpha:ℝ) by norm_num [alpha,interval])
    (show ((41719438469/50000000000):ℝ)*(interval.hi:ℝ)-(interval.hi:ℝ)*(1-interval.hi)≤(alpha:ℝ) by norm_num [alpha,interval])
  have hm := mul_le_mul_of_nonneg_right hcoef (hardCoreAvailableMean_nonneg G S B hz.le)
  have hnR : (S.card:ℝ)≤129 := by exact_mod_cast hN
  have hintercept : ((0/1):ℝ)*(S.card:ℝ)≤(varianceIntercept:ℝ) :=
    (mul_le_mul_of_nonneg_left hnR (by norm_num)).trans (by norm_num [varianceIntercept])
  nlinarith

#print axioms activity_bounds
#print axioms actual_variance

def availableWindow : MarkedAvailableWindow.Window := ⟨20,(51/101),(10429/20604),D⟩
theorem availableWindow_checked : availableWindow.check=true := by decide +kernel
#print axioms availableWindow_checked

theorem actual_available_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (_hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ))
    (_hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreAvailableVariance G S B z≤(D:ℝ)*hardCoreAvailableMean G S B z := by
  exact availableWindow.actual_available_variance availableWindow_checked hB hG hz
    (by simpa only [availableWindow,interval] using hq)

#print axioms actual_available_variance

def transferFactor : ℚ := (1/1)
theorem density_checked :
    0<ActivityPointDensityData.Point047.certificate.parameters.x ∧ ActivityPointDensityData.Point047.certificate.parameters.x≤activityLower ∧ 0≤transferFactor ∧
    transferFactor^2*ActivityPointDensityData.Point047.certificate.parameters.x*(1+activityLower)≤activityLower*(1+ActivityPointDensityData.Point047.certificate.parameters.x) ∧
    0≤ActivityPointDensityData.Point047.certificate.parameters.h ∧
    density≤transferFactor*(ActivityPointDensityData.Point047.certificate.parameters.r+ActivityPointDensityData.Point047.certificate.parameters.h/129) := by decide +kernel
#print axioms density_checked

theorem actual_density (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V)
    (h8 : 8≤S.card) (hN : S.card≤129) {z : ℝ} (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ))
    (_hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    (density:ℝ)*(S.card:ℝ)≤hardCoreMean G S z := by
  rcases density_checked with ⟨hx,hxa,hg,hfactor,hh,hrho⟩
  exact ActivityPointDensity.Certificate.finite_window_density
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point047.checked)
    (a:=(activityLower:ℝ)) (gamma:=(transferFactor:ℝ)) (rho:=(density:ℝ))
    G hG S h8 hN (by exact_mod_cast hx) (by exact_mod_cast hxa) (activity_bounds hz hq).1
    (by exact_mod_cast hg) (by exact_mod_cast hfactor) hh (by exact_mod_cast hrho)

#print axioms actual_density
end ForestUnimodality.Stage99SourceData.Cell069
