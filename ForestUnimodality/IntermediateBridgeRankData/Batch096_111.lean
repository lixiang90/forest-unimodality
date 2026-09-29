import ForestUnimodality.IntermediateBridgeRank
import ForestUnimodality.IntermediateBridgeCoverData.Batch096_111
import ForestUnimodality.ActivityPointDensityData.Point013
import ForestUnimodality.ActivityPointDensityData.Point014
import ForestUnimodality.ActivityPointDensityData.Point015
import ForestUnimodality.ActivityPointDensityData.Point016

namespace ForestUnimodality.IntermediateBridgeRankData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem band096_rank : band096.RankValid := by
  apply band096.rank_of_central
  decide +kernel
#print axioms band096_rank

theorem band097_rank : band097.RankValid := by
  exact band097.rank_of_certificate ActivityPointDensityData.Point013.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point013.checked)
    (1/1) (by decide +kernel)
#print axioms band097_rank

theorem band098_rank : band098.RankValid := by
  apply band098.rank_of_central
  decide +kernel
#print axioms band098_rank

theorem band099_rank : band099.RankValid := by
  apply band099.rank_of_central
  decide +kernel
#print axioms band099_rank

theorem band100_rank : band100.RankValid := by
  exact band100.rank_of_certificate ActivityPointDensityData.Point014.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point014.checked)
    (1/1) (by decide +kernel)
#print axioms band100_rank

theorem band101_rank : band101.RankValid := by
  exact band101.rank_of_certificate ActivityPointDensityData.Point014.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point014.checked)
    (1/1) (by decide +kernel)
#print axioms band101_rank

theorem band102_rank : band102.RankValid := by
  apply band102.rank_of_central
  decide +kernel
#print axioms band102_rank

theorem band103_rank : band103.RankValid := by
  apply band103.rank_of_central
  decide +kernel
#print axioms band103_rank

theorem band104_rank : band104.RankValid := by
  exact band104.rank_of_certificate ActivityPointDensityData.Point015.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point015.checked)
    (1/1) (by decide +kernel)
#print axioms band104_rank

theorem band105_rank : band105.RankValid := by
  exact band105.rank_of_certificate ActivityPointDensityData.Point015.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point015.checked)
    (1/1) (by decide +kernel)
#print axioms band105_rank

theorem band106_rank : band106.RankValid := by
  apply band106.rank_of_central
  decide +kernel
#print axioms band106_rank

theorem band107_rank : band107.RankValid := by
  apply band107.rank_of_central
  decide +kernel
#print axioms band107_rank

theorem band108_rank : band108.RankValid := by
  exact band108.rank_of_certificate ActivityPointDensityData.Point016.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point016.checked)
    (1/1) (by decide +kernel)
#print axioms band108_rank

theorem band109_rank : band109.RankValid := by
  exact band109.rank_of_certificate ActivityPointDensityData.Point016.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point016.checked)
    (1/1) (by decide +kernel)
#print axioms band109_rank

theorem band110_rank : band110.RankValid := by
  apply band110.rank_of_central
  decide +kernel
#print axioms band110_rank

theorem band111_rank : band111.RankValid := by
  apply band111.rank_of_central
  decide +kernel
#print axioms band111_rank

end ForestUnimodality.IntermediateBridgeRankData
