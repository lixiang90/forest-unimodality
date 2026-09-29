import ForestUnimodality.Stage80SourceData.Cell204.Auxiliary
import ForestUnimodality.Stage80LogVarianceData.Cell204
import ForestUnimodality.Stage80MessageSourceData.Case061.Actual

namespace ForestUnimodality.Stage80SourceData.Cell204
open Stage80KernelData.Cell204
variable {V : Type*} [DecidableEq V]

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 80≤S.card) (hN : S.card≤98) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ))
    (hmean : hardCoreMean G S z=k)
    (hm : hardCoreAvailableMean G S B z≤(mhi:ℝ)) :
    hardCoreVariance G S z≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+varianceIntercept := by
  exact Stage80LogVarianceData.Cell204.actual_variance_of_source_valid
    Stage80MessageSourceData.Case061.actual_source_valid k hB hG hn hN hz hq hmean hm

#print axioms actual_variance
end ForestUnimodality.Stage80SourceData.Cell204
