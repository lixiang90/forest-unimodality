import ForestUnimodality.IntermediateBridgeRank
import ForestUnimodality.IntermediateBridgeCoverData.Batch352_367
import ForestUnimodality.ActivityPointDensityData.Point077
import ForestUnimodality.ActivityPointDensityData.Point078
import ForestUnimodality.ActivityPointDensityData.Point079
import ForestUnimodality.ActivityPointDensityData.Point080

namespace ForestUnimodality.IntermediateBridgeRankData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem band352_rank : band352.RankValid := by
  exact band352.rank_of_certificate ActivityPointDensityData.Point077.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point077.checked)
    (1/1) (by decide +kernel)
#print axioms band352_rank

theorem band353_rank : band353.RankValid := by
  exact band353.rank_of_certificate ActivityPointDensityData.Point077.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point077.checked)
    (1/1) (by decide +kernel)
#print axioms band353_rank

theorem band354_rank : band354.RankValid := by
  exact band354.rank_of_certificate ActivityPointDensityData.Point077.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point077.checked)
    (1/1) (by decide +kernel)
#print axioms band354_rank

theorem band355_rank : band355.RankValid := by
  exact band355.rank_of_certificate ActivityPointDensityData.Point077.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point077.checked)
    (1/1) (by decide +kernel)
#print axioms band355_rank

theorem band356_rank : band356.RankValid := by
  exact band356.rank_of_certificate ActivityPointDensityData.Point078.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point078.checked)
    (1/1) (by decide +kernel)
#print axioms band356_rank

theorem band357_rank : band357.RankValid := by
  exact band357.rank_of_certificate ActivityPointDensityData.Point078.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point078.checked)
    (1/1) (by decide +kernel)
#print axioms band357_rank

theorem band358_rank : band358.RankValid := by
  exact band358.rank_of_certificate ActivityPointDensityData.Point078.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point078.checked)
    (1/1) (by decide +kernel)
#print axioms band358_rank

theorem band359_rank : band359.RankValid := by
  exact band359.rank_of_certificate ActivityPointDensityData.Point078.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point078.checked)
    (1/1) (by decide +kernel)
#print axioms band359_rank

theorem band360_rank : band360.RankValid := by
  exact band360.rank_of_certificate ActivityPointDensityData.Point079.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point079.checked)
    (1/1) (by decide +kernel)
#print axioms band360_rank

theorem band361_rank : band361.RankValid := by
  exact band361.rank_of_certificate ActivityPointDensityData.Point079.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point079.checked)
    (1/1) (by decide +kernel)
#print axioms band361_rank

theorem band362_rank : band362.RankValid := by
  exact band362.rank_of_certificate ActivityPointDensityData.Point079.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point079.checked)
    (1/1) (by decide +kernel)
#print axioms band362_rank

theorem band363_rank : band363.RankValid := by
  exact band363.rank_of_certificate ActivityPointDensityData.Point079.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point079.checked)
    (1/1) (by decide +kernel)
#print axioms band363_rank

theorem band364_rank : band364.RankValid := by
  exact band364.rank_of_certificate ActivityPointDensityData.Point080.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point080.checked)
    (1/1) (by decide +kernel)
#print axioms band364_rank

theorem band365_rank : band365.RankValid := by
  exact band365.rank_of_certificate ActivityPointDensityData.Point080.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point080.checked)
    (1/1) (by decide +kernel)
#print axioms band365_rank

theorem band366_rank : band366.RankValid := by
  exact band366.rank_of_certificate ActivityPointDensityData.Point080.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point080.checked)
    (1/1) (by decide +kernel)
#print axioms band366_rank

theorem band367_rank : band367.RankValid := by
  exact band367.rank_of_certificate ActivityPointDensityData.Point080.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point080.checked)
    (1/1) (by decide +kernel)
#print axioms band367_rank

end ForestUnimodality.IntermediateBridgeRankData
