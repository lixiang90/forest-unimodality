import ForestUnimodality.ActivityDensityTransfer
import ForestUnimodality.ImprovedSourceTail

/-! Certified nonnegative sources and the proved forest density supply the
entire fixed-independent-set tilt path used by the lower-tail budgets. -/
namespace ForestUnimodality
open Set
variable {V : Type*} [DecidableEq V]

theorem IsMaximumMarginalIndependentOn.tilt_variance_of_log_density
    {G : SimpleGraph V} {S B : Finset V} {z b A u v C ρ L : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hzb : z ≤ b) (hA : 0 ≤ A) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hvalid : NonnegativeSourceRowValid b A u v)
    (hρ : 0 < ρ) (hρq : ρ ≤ z / (1 + z)) (hL0 : L ≤ 0) (hL : L ≤ Real.log z)
    (hρL : ρ ≤ 276393 / 1000000 + (43 / 100) * L)
    (hCbound : A * (2 * (z / (1 + z)) / ρ - 1) ≤ C) :
    ∀ t ≥ 0, heterogeneousVariance G S (independentTiltActivities B z (Real.exp (-t)))
      (fun J => ((J ∩ B).card : ℝ)) ≤ C * hardCoreAvailableMean G S B z := by
  intro t ht
  have hact : ∀ x ∈ S, 0 ≤ independentTiltActivities B z (Real.exp (-t)) x ∧
      independentTiltActivities B z (Real.exp (-t)) x ≤ b := by
    intro x _
    have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
    unfold independentTiltActivities
    split_ifs
    · exact ⟨mul_nonneg (Real.exp_pos _).le hz.le,
        (by nlinarith : Real.exp (-t) * z ≤ z).trans hzb⟩
    · exact ⟨hz.le, hzb⟩
  have hs := forest_independent_constant_source_variance G hG S B hB.subset
    (independentTiltActivities B z (Real.exp (-t))) (hz.trans_le hzb) hact hu hv hvalid
  have hdensity := forest_mean_density_lower_of_log_enclosure G hG S hz hL0 hL hρL
  have hcard := hB.card_le_available_of_density hG hz hρ hρq hdensity
  have hm := hardCoreAvailableMean_nonneg G S B hz.le
  apply hs.trans
  calc
    A * (B.card : ℝ) ≤ A * ((2 * (z / (1 + z)) / ρ - 1) * hardCoreAvailableMean G S B z) :=
      mul_le_mul_of_nonneg_left hcard hA
    _ = (A * (2 * (z / (1 + z)) / ρ - 1)) * hardCoreAvailableMean G S B z := by ring
    _ ≤ C * hardCoreAvailableMean G S B z := mul_le_mul_of_nonneg_right hCbound hm

theorem IsMaximumMarginalIndependentOn.lowerTail_of_log_density
    {G : SimpleGraph V} {S B : Finset V} {z b A u v C ρ L α : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hzb : z ≤ b) (hA : 0 ≤ A) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hvalid : NonnegativeSourceRowValid b A u v)
    (hρ : 0 < ρ) (hρq : ρ ≤ z / (1 + z)) (hL0 : L ≤ 0) (hL : L ≤ Real.log z)
    (hρL : ρ ≤ 276393 / 1000000 + (43 / 100) * L)
    (hC : 0 < C) (hCbound : A * (2 * (z / (1 + z)) / ρ - 1) ≤ C)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    hardCoreAvailableLowerTail G S B z (α * hardCoreAvailableMean G S B z) ≤
      Real.exp (-((z / (1 + z)) ^ 2 * (1 - α) ^ 2 / (2 * C)) * hardCoreAvailableMean G S B z) := by
  exact hardCoreAvailableLowerTail_le_gaussian_rate G S B hB.subset hB.independent hz hC hα0 hα1
    (hB.tilt_variance_of_log_density hG hz hzb hA hu hv hvalid hρ hρq hL0 hL hρL hCbound)

theorem IsMaximumMarginalIndependentOn.corrected_lowerTail_of_log_density
    {G : SimpleGraph V} {S B : Finset V} {z b A u v C ρ L α t U E lo hi vmin qa rate : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hzb : z ≤ b) (hA : 0 ≤ A) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hvalid : NonnegativeSourceRowValid b A u v)
    (hρ : 0 < ρ) (hρq : ρ ≤ z / (1 + z)) (hL0 : L ≤ 0) (hL : L ≤ Real.log z)
    (hρL : ρ ≤ 276393 / 1000000 + (43 / 100) * L)
    (hCbound : A * (2 * (z / (1 + z)) / ρ - 1) ≤ C)
    (ht : 0 ≤ t) (htU : t ≤ U) (hE : 0 < E) (hexp : Real.exp U ≤ E)
    (hlo : lo ≤ z / (E + z)) (hhi : z / (1 + z) ≤ hi)
    (hvlo : vmin ≤ lo * (1 - lo)) (hvhi : vmin ≤ hi * (1 - hi))
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hqa : qa ≤ z / (1 + z))
    (hrate : rate ≤ qa * (1 - α) * t - (C - α * vmin) * t ^ 2 / 2) :
    hardCoreAvailableLowerTail G S B z (α * hardCoreAvailableMean G S B z) ≤
      Real.exp (-rate * hardCoreAvailableMean G S B z) := by
  apply hardCoreAvailableLowerTail_le_endpoint_corrected_rate G S B hB.subset hB.independent
    hz ht htU hE hexp hlo hhi hvlo hvhi hα0 hα1 hqa ?_ hrate
  intro x hx
  exact hB.tilt_variance_of_log_density hG hz hzb hA hu hv hvalid hρ hρq hL0 hL hρL hCbound x hx.1

#print axioms IsMaximumMarginalIndependentOn.tilt_variance_of_log_density
#print axioms IsMaximumMarginalIndependentOn.lowerTail_of_log_density
#print axioms IsMaximumMarginalIndependentOn.corrected_lowerTail_of_log_density
end ForestUnimodality
