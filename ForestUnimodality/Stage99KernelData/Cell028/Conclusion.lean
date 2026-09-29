import ForestUnimodality.BinomialKernel
import ForestUnimodality.Stage99KernelData.Cell028.Complete
import ForestUnimodality.Stage99SourceData.Cell028.Actual
import ForestUnimodality.ProbabilityDirectionBudget

/-! Actual graph consequences within the explicit activity and mean rectangle. -/
namespace ForestUnimodality.Stage99KernelData.Cell028

variable {V : Type*} [DecidableEq V]

theorem actual_kernel_positive {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z)
    (hG : G.IsAcyclic) (hS : 0 < S.card) (hN : S.card ≤ 129)
    (hz : 0 < z)
    (hq : z / (1 + z) ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ))
    (hrank : (S.card : ℝ) / 4 ≤ hardCoreMean G S z)
    (hmean : hardCoreMean G S z = k)
    (hm : hardCoreAvailableMean G S B z ∈ Set.Icc (mlo : ℝ) (mhi : ℝ)) :
    0 < averagedBinomialKernel G S B z row.wL row.wR row.wC k := by
  obtain ⟨hvarK, hvarM, hlap⟩ :=
    Stage99SourceData.Cell028.actual_inputs hB hG hz hS hq hrank
  have hbound := row.graphBudget_le_averaged interval row_checked
    (by decide +kernel : row.fixedIndices = ∅) 129
    (fun n hn j q hq => residual_nonneg_of_degree_le129 n hn j hq)
    G S B hB.subset hB.independent hN hz hq k hmean
    alpha varianceIntercept D (fun i => (rate i : ℝ)) hvarK hvarM hlap
  exact row.averaged_pos_of_graphBudget row_checked G S B z k
    alpha varianceIntercept D (fun i => (rate i : ℝ)) hbound (budget_positive hm)

theorem actual_left_coefficient_lt {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z)
    (hG : G.IsAcyclic) (hS : 0 < S.card) (hN : S.card ≤ 129)
    (hz : 0 < z) (hk : 1 ≤ k)
    (hq : z / (1 + z) ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ))
    (hrank : (S.card : ℝ) / 4 ≤ hardCoreMean G S z)
    (hmean : hardCoreMean G S z = k)
    (hm : hardCoreAvailableMean G S B z ∈ Set.Icc (mlo : ℝ) (mhi : ℝ)) :
    countIndependent G S (k - 1) < countIndependent G S k := by
  have hp := actual_kernel_positive k hB hG hS hN hz hq hrank hmean hm
  rw [averagedBinomialKernel_eq G S B hB.subset hB.independent hz _ _ _ hk] at hp
  have hl : 0 < tiltedLeft (countIndependent G S) z (partitionFunction G S z) k := by
    simpa only [row, Rat.cast_one, Rat.cast_zero, one_mul, zero_mul, add_zero] using hp
  exact ProbabilityDirectionBudget.left_coefficient_lt (countIndependent G S)
    hz (partitionFunction_pos G S hz.le) hk hl

theorem actual_no_weak_valley {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z)
    (hG : G.IsAcyclic) (hS : 0 < S.card) (hN : S.card ≤ 129)
    (hz : 0 < z) (hk : 1 ≤ k)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k)
    (hm : hardCoreAvailableMean G S B z∈Set.Icc (mlo:ℝ) (mhi:ℝ)) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  exact no_weak_valley_of_positive_binomial_kernel G S B hB.subset hB.independent
    (wL := (row.wL:ℝ)) (wR := (row.wR:ℝ)) (wC := (row.wC:ℝ)) hz
    (by norm_num [row]) (by norm_num [row]) (by norm_num [row]) hk
    (actual_kernel_positive k hB hG hS hN hz hq hrank hmean hm)

#print axioms actual_no_weak_valley

#print axioms actual_kernel_positive
#print axioms actual_left_coefficient_lt

end ForestUnimodality.Stage99KernelData.Cell028
