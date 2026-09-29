import ForestUnimodality.BasicFlowData.Cell013Term00.Complete

import ForestUnimodality.BasicFlowNormalized

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BasicFlowData.Cell013Term00
open BasicFlow


variable {V : Type*} [DecidableEq V]

theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hdensity : (rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) :=
  table.actual_laplace_normalized normalization_checked header_checked
    table_rows_checked connections_checked hB hG hz hq hdensity

#print axioms actual_laplace

end ForestUnimodality.BasicFlowData.Cell013Term00
