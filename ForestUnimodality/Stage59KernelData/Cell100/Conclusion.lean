import ForestUnimodality.Stage59KernelData.Cell100.Complete
import ForestUnimodality.Stage59KernelData.Cell100.Actual
import ForestUnimodality.FiniteMarginalKernel
import ForestUnimodality.ProbabilityDirectionBudget

/-! A checked matching-count rectangle, applied to actual forests.
This single rectangle does not assert coverage of the whole size-59 stage. -/
namespace ForestUnimodality.Stage59KernelData.Cell100
open FiniteMarginalSupport FiniteKernelRationalCertificate
variable {V : Type*} [DecidableEq V]

theorem actual_kernel_positive {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 59 ≤ S.card) (hN : S.card ≤ 79) (hz : 0 < z)
    (hq : z / (1 + z) ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ))
    (hrank : (S.card : ℝ) / 4 ≤ hardCoreMean G S z)
    (hmean : hardCoreMean G S z = k)
    (hhalf : 2*k≤S.card)
    (hm : hardCoreAvailableMean G S B z ∈ Set.Icc (mlo : ℝ) (mhi : ℝ)) :
    0 < averagedBinomialKernel G S B z row.wL row.wR row.wC k := by
  have hpairs := actual_pair k hB hG hn hN hz hq hrank hmean hhalf hm.2
  have hab := activity_bounds hz hq
  have hcount : ∀ j ∈ row.fixedIndices,
      hardCoreFixedShiftMass G S B z k j ≤ (countBound j : ℝ) := by
    intro j hj
    apply (actual_joint_count_bound hG hB hz (by norm_num [activityLower]) hab.1 hab.2 k j pairs hpairs).trans
    exact_mod_cast count_bounds_checked j hj
  have hbound := row.supportBudget_le_averaged interval row_checked 79
    (fun n j => geometrySupportCheck pairs n j = true)
    (fun n hn j hs q hq => residual_nonneg_of_degree_le79 n hn j hs hq)
    G S B hB.subset hB.independent hN hz hq k hmean
    (fun _ _ _ _ hw => actual_geometry_support hG hB hz k pairs hpairs hw)
    alpha 0 D (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ))
    (actual_variance hB hG hn hN hz hq)
    (actual_available_variance hB hG hz (by omega) hq hrank)
    (actual_laplace hB hG hn hN hz hq hrank) hcount
  exact row.averaged_pos_of_supportBudget row_checked G S B z k
    alpha 0 D (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ))
    hbound (by simpa [budget, varianceIntercept] using budget_positive hm)

theorem actual_no_weak_valley {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 59 ≤ S.card) (hN : S.card ≤ 79) (hz : 0 < z)
    (hq : z / (1 + z) ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ))
    (hrank : (S.card : ℝ) / 4 ≤ hardCoreMean G S z)
    (hmean : hardCoreMean G S z = k)
    (hhalf : 2*k≤S.card)
    (hm : hardCoreAvailableMean G S B z ∈ Set.Icc (mlo : ℝ) (mhi : ℝ)) :
    ¬ (countIndependent G S k ≤ countIndependent G S (k-1) ∧
      countIndependent G S k ≤ countIndependent G S (k+1)) := by
  have hnR : (59 : ℝ) ≤ S.card := by exact_mod_cast hn
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by linarith
  have hk : 1 ≤ k := by exact_mod_cast hkR
  exact row.no_weak_valley_of_positive_averaged row_checked hB.subset hB.independent hz k hk
    (actual_kernel_positive k hB hG hn hN hz hq hrank hmean hhalf hm)

#print axioms actual_kernel_positive
#print axioms actual_no_weak_valley
end ForestUnimodality.Stage59KernelData.Cell100
