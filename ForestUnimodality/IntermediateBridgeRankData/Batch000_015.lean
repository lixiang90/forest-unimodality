import ForestUnimodality.IntermediateBridgeRank
import ForestUnimodality.IntermediateBridgeCoverData.Batch000_015

namespace ForestUnimodality.IntermediateBridgeRankData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem band000_rank : band000.RankValid := by
  apply band000.rank_of_central
  decide +kernel
#print axioms band000_rank

theorem band001_rank : band001.RankValid := by
  apply band001.rank_of_central
  decide +kernel
#print axioms band001_rank

theorem band002_rank : band002.RankValid := by
  apply band002.rank_of_central
  decide +kernel
#print axioms band002_rank

theorem band003_rank : band003.RankValid := by
  apply band003.rank_of_central
  decide +kernel
#print axioms band003_rank

theorem band004_rank : band004.RankValid := by
  apply band004.rank_of_central
  decide +kernel
#print axioms band004_rank

theorem band005_rank : band005.RankValid := by
  apply band005.rank_of_central
  decide +kernel
#print axioms band005_rank

theorem band006_rank : band006.RankValid := by
  apply band006.rank_of_central
  decide +kernel
#print axioms band006_rank

theorem band007_rank : band007.RankValid := by
  apply band007.rank_of_central
  decide +kernel
#print axioms band007_rank

theorem band008_rank : band008.RankValid := by
  apply band008.rank_of_central
  decide +kernel
#print axioms band008_rank

theorem band009_rank : band009.RankValid := by
  apply band009.rank_of_central
  decide +kernel
#print axioms band009_rank

theorem band010_rank : band010.RankValid := by
  apply band010.rank_of_central
  decide +kernel
#print axioms band010_rank

theorem band011_rank : band011.RankValid := by
  apply band011.rank_of_central
  decide +kernel
#print axioms band011_rank

theorem band012_rank : band012.RankValid := by
  apply band012.rank_of_central
  decide +kernel
#print axioms band012_rank

theorem band013_rank : band013.RankValid := by
  apply band013.rank_of_central
  decide +kernel
#print axioms band013_rank

theorem band014_rank : band014.RankValid := by
  apply band014.rank_of_central
  decide +kernel
#print axioms band014_rank

theorem band015_rank : band015.RankValid := by
  apply band015.rank_of_central
  decide +kernel
#print axioms band015_rank

end ForestUnimodality.IntermediateBridgeRankData
