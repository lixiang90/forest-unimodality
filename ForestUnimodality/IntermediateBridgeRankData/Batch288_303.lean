import ForestUnimodality.IntermediateBridgeRank
import ForestUnimodality.IntermediateBridgeCoverData.Batch288_303
import ForestUnimodality.ActivityPointDensityData.Point061
import ForestUnimodality.ActivityPointDensityData.Point062
import ForestUnimodality.ActivityPointDensityData.Point063
import ForestUnimodality.ActivityPointDensityData.Point064

namespace ForestUnimodality.IntermediateBridgeRankData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem band288_rank : band288.RankValid := by
  exact band288.rank_of_certificate ActivityPointDensityData.Point061.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point061.checked)
    (1/1) (by decide +kernel)
#print axioms band288_rank

theorem band289_rank : band289.RankValid := by
  exact band289.rank_of_certificate ActivityPointDensityData.Point061.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point061.checked)
    (1/1) (by decide +kernel)
#print axioms band289_rank

theorem band290_rank : band290.RankValid := by
  exact band290.rank_of_certificate ActivityPointDensityData.Point061.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point061.checked)
    (1/1) (by decide +kernel)
#print axioms band290_rank

theorem band291_rank : band291.RankValid := by
  exact band291.rank_of_certificate ActivityPointDensityData.Point061.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point061.checked)
    (1/1) (by decide +kernel)
#print axioms band291_rank

theorem band292_rank : band292.RankValid := by
  exact band292.rank_of_certificate ActivityPointDensityData.Point062.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point062.checked)
    (1/1) (by decide +kernel)
#print axioms band292_rank

theorem band293_rank : band293.RankValid := by
  exact band293.rank_of_certificate ActivityPointDensityData.Point062.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point062.checked)
    (1/1) (by decide +kernel)
#print axioms band293_rank

theorem band294_rank : band294.RankValid := by
  exact band294.rank_of_certificate ActivityPointDensityData.Point062.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point062.checked)
    (1/1) (by decide +kernel)
#print axioms band294_rank

theorem band295_rank : band295.RankValid := by
  exact band295.rank_of_certificate ActivityPointDensityData.Point062.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point062.checked)
    (1/1) (by decide +kernel)
#print axioms band295_rank

theorem band296_rank : band296.RankValid := by
  exact band296.rank_of_certificate ActivityPointDensityData.Point063.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point063.checked)
    (1/1) (by decide +kernel)
#print axioms band296_rank

theorem band297_rank : band297.RankValid := by
  exact band297.rank_of_certificate ActivityPointDensityData.Point063.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point063.checked)
    (1/1) (by decide +kernel)
#print axioms band297_rank

theorem band298_rank : band298.RankValid := by
  exact band298.rank_of_certificate ActivityPointDensityData.Point063.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point063.checked)
    (1/1) (by decide +kernel)
#print axioms band298_rank

theorem band299_rank : band299.RankValid := by
  exact band299.rank_of_certificate ActivityPointDensityData.Point063.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point063.checked)
    (1/1) (by decide +kernel)
#print axioms band299_rank

theorem band300_rank : band300.RankValid := by
  exact band300.rank_of_certificate ActivityPointDensityData.Point064.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point064.checked)
    (1/1) (by decide +kernel)
#print axioms band300_rank

theorem band301_rank : band301.RankValid := by
  exact band301.rank_of_certificate ActivityPointDensityData.Point064.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point064.checked)
    (1/1) (by decide +kernel)
#print axioms band301_rank

theorem band302_rank : band302.RankValid := by
  exact band302.rank_of_certificate ActivityPointDensityData.Point064.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point064.checked)
    (1/1) (by decide +kernel)
#print axioms band302_rank

theorem band303_rank : band303.RankValid := by
  exact band303.rank_of_certificate ActivityPointDensityData.Point064.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point064.checked)
    (1/1) (by decide +kernel)
#print axioms band303_rank

end ForestUnimodality.IntermediateBridgeRankData
