import ForestUnimodality.Stage59KernelData.Cell000.Complete
import ForestUnimodality.Stage59KernelData.Cell000.Actual
import ForestUnimodality.FiniteMarginalKernel
import ForestUnimodality.ProbabilityDirectionBudget

/-! First complete matching-count rectangle, applied to actual forests.
This single rectangle does not assert coverage of the whole size-59 stage. -/
namespace ForestUnimodality.Stage59KernelData.Cell000
open FiniteMarginalSupport FiniteKernelRationalCertificate
variable {V : Type*} [DecidableEq V]

theorem actual_kernel_positive {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 59 ≤ S.card) (hN : S.card ≤ 79) (hz : 0 < z)
    (hq : z / (1 + z) ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ))
    (hrank : (S.card : ℝ) / 4 ≤ hardCoreMean G S z)
    (hmean : hardCoreMean G S z = k)
    (hm : hardCoreAvailableMean G S B z ∈ Set.Icc (mlo : ℝ) (mhi : ℝ)) :
    0 < averagedBinomialKernel G S B z row.wL row.wR row.wC k := by
  have hpairs := actual_pair k hB hG hn hN hz hq hrank hmean hm.2
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
    alpha 0 D (fun i => Fin.elim0 i) (fun j => (countBound j : ℝ))
    (actual_variance hB hG hz hq)
    (actual_available_variance hB hG hz (by omega) hq hrank)
    (fun i _ => Fin.elim0 i) hcount
  exact row.averaged_pos_of_supportBudget row_checked G S B z k
    alpha 0 D (fun i => Fin.elim0 i) (fun j => (countBound j : ℝ))
    hbound (budget_positive hm)

theorem actual_left_coefficient_lt {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 59 ≤ S.card) (hN : S.card ≤ 79) (hz : 0 < z)
    (hq : z / (1 + z) ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ))
    (hrank : (S.card : ℝ) / 4 ≤ hardCoreMean G S z)
    (hmean : hardCoreMean G S z = k)
    (hm : hardCoreAvailableMean G S B z ∈ Set.Icc (mlo : ℝ) (mhi : ℝ)) :
    countIndependent G S (k-1) < countIndependent G S k := by
  have hnR : (59 : ℝ) ≤ S.card := by exact_mod_cast hn
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by linarith
  have hk : 1 ≤ k := by exact_mod_cast hkR
  have hp := actual_kernel_positive k hB hG hn hN hz hq hrank hmean hm
  rw [averagedBinomialKernel_eq G S B hB.subset hB.independent hz _ _ _ hk] at hp
  have hleft : 0 < 4 * tiltedLeft (countIndependent G S) z (partitionFunction G S z) k := by
    simpa only [row, Rat.cast_ofNat, Rat.cast_zero, zero_mul, add_zero] using hp
  have hl : 0 < tiltedLeft (countIndependent G S) z (partitionFunction G S z) k := by linarith
  exact ProbabilityDirectionBudget.left_coefficient_lt (countIndependent G S)
    hz (partitionFunction_pos G S hz.le) hk hl

#print axioms actual_kernel_positive
#print axioms actual_left_coefficient_lt
end ForestUnimodality.Stage59KernelData.Cell000

