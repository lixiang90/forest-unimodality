import ForestUnimodality.IntermediateBridgeRank
import ForestUnimodality.IntermediateBridgeCoverData.Batch112_127
import ForestUnimodality.ActivityPointDensityData.Point017
import ForestUnimodality.ActivityPointDensityData.Point018
import ForestUnimodality.ActivityPointDensityData.Point019
import ForestUnimodality.ActivityPointDensityData.Point020

namespace ForestUnimodality.IntermediateBridgeRankData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem band112_rank : band112.RankValid := by
  exact band112.rank_of_certificate ActivityPointDensityData.Point017.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point017.checked)
    (1/1) (by decide +kernel)
#print axioms band112_rank

theorem band113_rank : band113.RankValid := by
  exact band113.rank_of_certificate ActivityPointDensityData.Point017.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point017.checked)
    (1/1) (by decide +kernel)
#print axioms band113_rank

theorem band114_rank : band114.RankValid := by
  apply band114.rank_of_central
  decide +kernel
#print axioms band114_rank

theorem band115_rank : band115.RankValid := by
  apply band115.rank_of_central
  decide +kernel
#print axioms band115_rank

theorem band116_rank : band116.RankValid := by
  exact band116.rank_of_certificate ActivityPointDensityData.Point018.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point018.checked)
    (1/1) (by decide +kernel)
#print axioms band116_rank

theorem band117_rank : band117.RankValid := by
  exact band117.rank_of_certificate ActivityPointDensityData.Point018.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point018.checked)
    (1/1) (by decide +kernel)
#print axioms band117_rank

theorem band118_rank : band118.RankValid := by
  apply band118.rank_of_central
  decide +kernel
#print axioms band118_rank

theorem band119_rank : band119.RankValid := by
  apply band119.rank_of_central
  decide +kernel
#print axioms band119_rank

theorem band120_rank : band120.RankValid := by
  exact band120.rank_of_certificate ActivityPointDensityData.Point019.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point019.checked)
    (1/1) (by decide +kernel)
#print axioms band120_rank

theorem band121_rank : band121.RankValid := by
  exact band121.rank_of_certificate ActivityPointDensityData.Point019.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point019.checked)
    (1/1) (by decide +kernel)
#print axioms band121_rank

theorem band122_rank : band122.RankValid := by
  exact band122.rank_of_certificate ActivityPointDensityData.Point019.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point019.checked)
    (1/1) (by decide +kernel)
#print axioms band122_rank

theorem band123_rank : band123.RankValid := by
  apply band123.rank_of_central
  decide +kernel
#print axioms band123_rank

theorem band124_rank : band124.RankValid := by
  exact band124.rank_of_certificate ActivityPointDensityData.Point020.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point020.checked)
    (1/1) (by decide +kernel)
#print axioms band124_rank

theorem band125_rank : band125.RankValid := by
  exact band125.rank_of_certificate ActivityPointDensityData.Point020.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point020.checked)
    (1/1) (by decide +kernel)
#print axioms band125_rank

theorem band126_rank : band126.RankValid := by
  exact band126.rank_of_certificate ActivityPointDensityData.Point020.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point020.checked)
    (1/1) (by decide +kernel)
#print axioms band126_rank

theorem band127_rank : band127.RankValid := by
  apply band127.rank_of_central
  decide +kernel
#print axioms band127_rank

end ForestUnimodality.IntermediateBridgeRankData
