import ForestUnimodality.IntermediateBridgeRank
import ForestUnimodality.IntermediateBridgeCoverData.Batch400_415
import ForestUnimodality.ActivityPointDensityData.Point089
import ForestUnimodality.ActivityPointDensityData.Point090
import ForestUnimodality.ActivityPointDensityData.Point091
import ForestUnimodality.ActivityPointDensityData.Point092

namespace ForestUnimodality.IntermediateBridgeRankData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem band400_rank : band400.RankValid := by
  exact band400.rank_of_certificate ActivityPointDensityData.Point089.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point089.checked)
    (1/1) (by decide +kernel)
#print axioms band400_rank

theorem band401_rank : band401.RankValid := by
  exact band401.rank_of_certificate ActivityPointDensityData.Point089.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point089.checked)
    (1/1) (by decide +kernel)
#print axioms band401_rank

theorem band402_rank : band402.RankValid := by
  exact band402.rank_of_certificate ActivityPointDensityData.Point089.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point089.checked)
    (1/1) (by decide +kernel)
#print axioms band402_rank

theorem band403_rank : band403.RankValid := by
  exact band403.rank_of_certificate ActivityPointDensityData.Point089.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point089.checked)
    (1/1) (by decide +kernel)
#print axioms band403_rank

theorem band404_rank : band404.RankValid := by
  exact band404.rank_of_certificate ActivityPointDensityData.Point090.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point090.checked)
    (1/1) (by decide +kernel)
#print axioms band404_rank

theorem band405_rank : band405.RankValid := by
  exact band405.rank_of_certificate ActivityPointDensityData.Point090.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point090.checked)
    (1/1) (by decide +kernel)
#print axioms band405_rank

theorem band406_rank : band406.RankValid := by
  exact band406.rank_of_certificate ActivityPointDensityData.Point090.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point090.checked)
    (1/1) (by decide +kernel)
#print axioms band406_rank

theorem band407_rank : band407.RankValid := by
  exact band407.rank_of_certificate ActivityPointDensityData.Point090.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point090.checked)
    (1/1) (by decide +kernel)
#print axioms band407_rank

theorem band408_rank : band408.RankValid := by
  exact band408.rank_of_certificate ActivityPointDensityData.Point091.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point091.checked)
    (1/1) (by decide +kernel)
#print axioms band408_rank

theorem band409_rank : band409.RankValid := by
  exact band409.rank_of_certificate ActivityPointDensityData.Point091.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point091.checked)
    (1/1) (by decide +kernel)
#print axioms band409_rank

theorem band410_rank : band410.RankValid := by
  exact band410.rank_of_certificate ActivityPointDensityData.Point091.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point091.checked)
    (1/1) (by decide +kernel)
#print axioms band410_rank

theorem band411_rank : band411.RankValid := by
  exact band411.rank_of_certificate ActivityPointDensityData.Point091.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point091.checked)
    (1/1) (by decide +kernel)
#print axioms band411_rank

theorem band412_rank : band412.RankValid := by
  exact band412.rank_of_certificate ActivityPointDensityData.Point092.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point092.checked)
    (1/1) (by decide +kernel)
#print axioms band412_rank

theorem band413_rank : band413.RankValid := by
  exact band413.rank_of_certificate ActivityPointDensityData.Point092.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point092.checked)
    (1/1) (by decide +kernel)
#print axioms band413_rank

theorem band414_rank : band414.RankValid := by
  exact band414.rank_of_certificate ActivityPointDensityData.Point092.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point092.checked)
    (1/1) (by decide +kernel)
#print axioms band414_rank

theorem band415_rank : band415.RankValid := by
  exact band415.rank_of_certificate ActivityPointDensityData.Point092.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point092.checked)
    (1/1) (by decide +kernel)
#print axioms band415_rank

end ForestUnimodality.IntermediateBridgeRankData
