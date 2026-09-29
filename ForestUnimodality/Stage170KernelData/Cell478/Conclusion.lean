import ForestUnimodality.BinomialKernel
import ForestUnimodality.Stage170KernelData.Cell478.Complete
import ForestUnimodality.Stage170SourceData.Cell478.Actual
import ForestUnimodality.ProbabilityDirectionBudget

/-! This finite rectangle controls the actual independence
coefficients. The activity and available-mean rectangle hypotheses are
explicit; this one rectangle does not cover every graph of order 170–349. -/
namespace ForestUnimodality.Stage170KernelData.Cell478

variable {V : Type*} [DecidableEq V]

theorem actual_kernel_positive {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z)
    (hG : G.IsAcyclic) (hS : 0 < S.card) (hN : S.card ≤ 349)
    (hz : 0 < z)
    (hq : z / (1 + z) ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ))
    (hrank : (S.card : ℝ) / 4 ≤ hardCoreMean G S z)
    (hmean : hardCoreMean G S z = k)
    (hm : hardCoreAvailableMean G S B z ∈ Set.Icc (mlo : ℝ) (mhi : ℝ)) :
    0 < averagedBinomialKernel G S B z row.wL row.wR row.wC k := by
  obtain ⟨hvarK, hvarM, hlap⟩ :=
    Stage170SourceData.Cell478.actual_inputs hB hG hz hS hq hrank
  have hbound := row.graphBudget_le_averaged interval row_checked
    (by decide +kernel : row.fixedIndices = ∅) 349
    (fun n hn j q hq => residual_nonneg_of_degree_le349 n hn j hq)
    G S B hB.subset hB.independent hN hz hq k hmean
    (R * vmax : ℚ) 0 D (fun i => (rate i : ℝ)) hvarK hvarM hlap
  exact row.averaged_pos_of_graphBudget row_checked G S B z k
    (R * vmax : ℚ) 0 D (fun i => (rate i : ℝ)) hbound (budget_positive hm)

theorem actual_no_weak_valley {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z)
    (hG : G.IsAcyclic) (hS : 0 < S.card) (hN : S.card ≤ 349)
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

end ForestUnimodality.Stage170KernelData.Cell478
