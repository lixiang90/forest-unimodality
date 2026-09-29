import ForestUnimodality.Stage99KernelData.Cell028.Budget
import ForestUnimodality.Stage80MessageSourceData.Case055.Actual
import ForestUnimodality.LogVarianceProfile
import ForestUnimodality.FiniteMeanVarianceProfile
import ForestUnimodality.Stage170SourceData.Windows.Batch020_039

/-! Actual graph profiles only. Finite kernel and Laplace bounds are separate. -/
namespace ForestUnimodality.Stage99SourceData.Cell028
open Stage99KernelData.Cell028
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def activityLower : ℚ := (17/20)
def activityUpper : ℚ := (1613/1865)
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
    (hS : 0<S.card) (hN : S.card≤129) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ))
    (hm : hardCoreAvailableMean G S B z∈Set.Icc (mlo:ℝ) (mhi:ℝ)) :
    hardCoreVariance G S z≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+varianceIntercept := by
  have hab := activity_bounds hz hq
  have hlo : (Stage80MessageSourceData.Case055.parameters.lower:ℝ)≤z := by
    norm_num [Stage80MessageSourceData.Case055.parameters, Stage80MessagePriceData.case055, MessagePriceSpline.Parameters.toReal,activityLower] at hab ⊢
    linarith
  have hhi : z≤(Stage80MessageSourceData.Case055.parameters.upper:ℝ) := by
    norm_num [Stage80MessageSourceData.Case055.parameters, Stage80MessagePriceData.case055, MessagePriceSpline.Parameters.toReal,activityUpper] at hab ⊢
    linarith
  have hv := Stage80MessageSourceData.Case055.actual_variance_le_mass hB hG (Finset.card_pos.mp hS) hlo hhi
  rw [hardCoreOccupiedMass_eq_activity_available_mean G S B hB.subset hB.independent hz] at hv
  have hlin : hardCoreVariance G S z≤((23674014590257/25000000000000):ℝ)*
      (z/(1+z)*hardCoreAvailableMean G S B z)+((8937591/100000000000000):ℝ)*(S.card:ℝ) := by
    norm_num [Stage80MessageSourceData.Case055.parameters, Stage80MessagePriceData.case055, MessagePriceSpline.Parameters.toReal] at hv ⊢
    exact hv
  exact bounded_mean_variance_profile (C:=((23674014590257/25000000000000):ℝ))
    (D:=((8937591/100000000000000):ℝ)) (delta:=((-2408457297224483201000000000014517/151206050000000000000000000000000000):ℝ))
    hq hm (hardCoreAvailableMean_nonneg G S B hz.le)
    (show (S.card:ℝ)≤129 by exact_mod_cast hN) (by norm_num)
    (by norm_num [interval,alpha]) (by norm_num [interval,alpha])
    (by norm_num [mlo,varianceIntercept]) (by norm_num [mhi,varianceIntercept]) hlin

#print axioms activity_bounds
#print axioms actual_variance

theorem actual_available_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreAvailableVariance G S B z≤(D:ℝ)*hardCoreAvailableMean G S B z := by
  have hqw : z/(1+z)∈Set.Icc (Stage170SourceData.Window028.window.qa:ℝ) (Stage170SourceData.Window028.window.qb:ℝ) := by
    norm_num [Stage170SourceData.Window028.window,interval] at hq ⊢
    constructor <;> linarith [hq.1,hq.2]
  have hv := Stage170SourceData.Window028.window.available_variance Stage170SourceData.Window028.valid hB hG hz hS hqw hrank
  exact hv.trans (mul_le_mul_of_nonneg_right
    (show (Stage170SourceData.Window028.window.D:ℝ)≤(D:ℝ) by norm_num [Stage170SourceData.Window028.window,D])
    (hardCoreAvailableMean_nonneg G S B hz.le))

#print axioms actual_available_variance

theorem actual_density (G : SimpleGraph V) (_hG : G.IsAcyclic) (S : Finset V)
    (_h8 : 8≤S.card) (_hN : S.card≤129) {z : ℝ} (_hz : 0<z)
    (_hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    (density:ℝ)*(S.card:ℝ)≤hardCoreMean G S z := by
  have hρ : (density:ℝ)≤1/4 := by norm_num [density]
  have hm := mul_le_mul_of_nonneg_right hρ (show (0:ℝ)≤S.card by positivity)
  nlinarith

#print axioms actual_density
end ForestUnimodality.Stage99SourceData.Cell028
