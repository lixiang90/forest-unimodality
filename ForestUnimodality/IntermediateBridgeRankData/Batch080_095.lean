import ForestUnimodality.IntermediateBridgeRank
import ForestUnimodality.IntermediateBridgeCoverData.Batch080_095
import ForestUnimodality.ActivityPointDensityData.Point012

namespace ForestUnimodality.IntermediateBridgeRankData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem band080_rank : band080.RankValid := by
  apply band080.rank_of_central
  decide +kernel
#print axioms band080_rank

theorem band081_rank : band081.RankValid := by
  apply band081.rank_of_central
  decide +kernel
#print axioms band081_rank

theorem band082_rank : band082.RankValid := by
  apply band082.rank_of_central
  decide +kernel
#print axioms band082_rank

theorem band083_rank : band083.RankValid := by
  apply band083.rank_of_central
  decide +kernel
#print axioms band083_rank

theorem band084_rank : band084.RankValid := by
  apply band084.rank_of_central
  decide +kernel
#print axioms band084_rank

theorem band085_rank : band085.RankValid := by
  apply band085.rank_of_central
  decide +kernel
#print axioms band085_rank

theorem band086_rank : band086.RankValid := by
  apply band086.rank_of_central
  decide +kernel
#print axioms band086_rank

theorem band087_rank : band087.RankValid := by
  apply band087.rank_of_central
  decide +kernel
#print axioms band087_rank

theorem band088_rank : band088.RankValid := by
  apply band088.rank_of_central
  decide +kernel
#print axioms band088_rank

theorem band089_rank : band089.RankValid := by
  apply band089.rank_of_central
  decide +kernel
#print axioms band089_rank

theorem band090_rank : band090.RankValid := by
  apply band090.rank_of_central
  decide +kernel
#print axioms band090_rank

theorem band091_rank : band091.RankValid := by
  apply band091.rank_of_central
  decide +kernel
#print axioms band091_rank

theorem band092_rank : band092.RankValid := by
  apply band092.rank_of_central
  decide +kernel
#print axioms band092_rank

theorem band093_rank : band093.RankValid := by
  exact band093.rank_of_certificate ActivityPointDensityData.Point012.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point012.checked)
    (1/1) (by decide +kernel)
#print axioms band093_rank

theorem band094_rank : band094.RankValid := by
  apply band094.rank_of_central
  decide +kernel
#print axioms band094_rank

theorem band095_rank : band095.RankValid := by
  apply band095.rank_of_central
  decide +kernel
#print axioms band095_rank

end ForestUnimodality.IntermediateBridgeRankData
