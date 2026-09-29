import ForestUnimodality.Stage80ConstantWindow
import ForestUnimodality.LogVarianceProfile

/-! Preserve the joint probability dependence of a proved constant source.
This avoids separately maximizing the variance ratio and Bernoulli variance. -/
namespace ForestUnimodality.Stage80ConstantWindow

variable {V : Type*} [DecidableEq V]

theorem Window.exact_total_variance (w : Window) (hw : w.check = true) (alpha : ℚ)
    (hlo : Stage80ConstantLibrary.factor w.source * w.qa - w.qa * (1-w.qa) ≤ alpha)
    (hhi : Stage80ConstantLibrary.factor w.source * w.qb - w.qb * (1-w.qb) ≤ alpha)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hq : z/(1+z) ∈ Set.Icc (w.qa : ℝ) (w.qb : ℝ)) :
    hardCoreVariance G S z ≤
      (z/(1+z)*(1-z/(1+z)) + (alpha : ℝ)) * hardCoreAvailableMean G S B z + 0 := by
  have hab := w.activity_bounds hw hz hq
  have hv := Stage80ConstantLibrary.actual_variance_le_mass w.source hB hG hab.1 hab.2
  rw [hardCoreOccupiedMass_eq_activity_available_mean G S B hB.subset hB.independent hz] at hv
  have hprofile := quadratic_profile_of_endpoints
    (C := (Stage80ConstantLibrary.factor w.source : ℝ)) (alpha := (alpha : ℝ)) hq
    (by exact_mod_cast hlo) (by exact_mod_cast hhi)
  have hbound := mul_le_mul_of_nonneg_right hprofile
    (hardCoreAvailableMean_nonneg G S B hz.le)
  nlinarith

#print axioms Window.exact_total_variance
end ForestUnimodality.Stage80ConstantWindow
