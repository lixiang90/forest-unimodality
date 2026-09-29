import ForestUnimodality.Stage130KernelData.Cell031.Budget
import ForestUnimodality.Stage80MessageSourceData.Case001.Actual
import ForestUnimodality.LogVarianceProfile
import ForestUnimodality.Stage170SourceData.Windows.Batch080_099

/-! Actual graph profiles only. Finite kernel and Laplace bounds are separate. -/
namespace ForestUnimodality.Stage130SourceData.Cell031
open Stage130KernelData.Cell031
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def activityLower : ℚ := (1677/1895)
def activityUpper : ℚ := (841/945)
def density : ℚ := (1/4)

theorem activity_bounds {z : ℝ} (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ)) :
    (activityLower:ℝ)≤z ∧ z≤(activityUpper:ℝ) := by
  have hl := (le_div_iff₀ (by positivity : 0<1+z)).mp hq.1
  have hu := (div_le_iff₀ (by positivity : 0<1+z)).mp hq.2
  norm_num [interval,activityLower,activityUpper] at hl hu ⊢
  constructor <;> linarith

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hS : 0<S.card) (hN : S.card≤169) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ)) :
    hardCoreVariance G S z≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+varianceIntercept := by
  have hab := activity_bounds hz hq
  have hlo : (Stage80MessageSourceData.Case001.parameters.lower:ℝ)≤z := by
    norm_num [Stage80MessageSourceData.Case001.parameters, Stage80MessagePriceData.case001, MessagePriceSpline.Parameters.toReal,activityLower] at hab ⊢
    linarith
  have hhi : z≤(Stage80MessageSourceData.Case001.parameters.upper:ℝ) := by
    norm_num [Stage80MessageSourceData.Case001.parameters, Stage80MessagePriceData.case001, MessagePriceSpline.Parameters.toReal,activityUpper] at hab ⊢
    linarith
  have hv := Stage80MessageSourceData.Case001.actual_variance_le_mass hB hG (Finset.card_pos.mp hS) hlo hhi
  rw [hardCoreOccupiedMass_eq_activity_available_mean G S B hB.subset hB.independent hz] at hv
  have hlin : hardCoreVariance G S z≤((2862417566689/3125000000000):ℝ)*
      (z/(1+z)*hardCoreAvailableMean G S B z)+((0/1):ℝ)*(S.card:ℝ) := by
    norm_num [Stage80MessageSourceData.Case001.parameters, Stage80MessagePriceData.case001, MessagePriceSpline.Parameters.toReal] at hv ⊢
    exact hv
  have hcoef := quadratic_profile_of_endpoints (C:=((2862417566689/3125000000000):ℝ)) hq
    (show ((2862417566689/3125000000000):ℝ)*(interval.lo:ℝ)-(interval.lo:ℝ)*(1-interval.lo)≤(alpha:ℝ) by norm_num [alpha,interval])
    (show ((2862417566689/3125000000000):ℝ)*(interval.hi:ℝ)-(interval.hi:ℝ)*(1-interval.hi)≤(alpha:ℝ) by norm_num [alpha,interval])
  have hm := mul_le_mul_of_nonneg_right hcoef (hardCoreAvailableMean_nonneg G S B hz.le)
  have hnR : (S.card:ℝ)≤169 := by exact_mod_cast hN
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
  have hqw : z/(1+z)∈Set.Icc (Stage170SourceData.Window080.window.qa:ℝ) (Stage170SourceData.Window080.window.qb:ℝ) := by
    norm_num [Stage170SourceData.Window080.window,interval] at hq ⊢
    constructor <;> linarith [hq.1,hq.2]
  have hv := Stage170SourceData.Window080.window.available_variance Stage170SourceData.Window080.valid hB hG hz hS hqw hrank
  exact hv.trans (mul_le_mul_of_nonneg_right
    (show (Stage170SourceData.Window080.window.D:ℝ)≤(D:ℝ) by norm_num [Stage170SourceData.Window080.window,D])
    (hardCoreAvailableMean_nonneg G S B hz.le))

#print axioms actual_available_variance

theorem actual_density (G : SimpleGraph V) (_hG : G.IsAcyclic) (S : Finset V)
    (_h8 : 8≤S.card) (_hN : S.card≤169) {z : ℝ} (_hz : 0<z)
    (_hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    (density:ℝ)*(S.card:ℝ)≤hardCoreMean G S z := by
  have hρ : (density:ℝ)≤1/4 := by norm_num [density]
  have hm := mul_le_mul_of_nonneg_right hρ (show (0:ℝ)≤S.card by positivity)
  nlinarith

#print axioms actual_density
end ForestUnimodality.Stage130SourceData.Cell031
