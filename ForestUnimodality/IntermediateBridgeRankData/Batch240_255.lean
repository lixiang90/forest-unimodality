import ForestUnimodality.IntermediateBridgeRank
import ForestUnimodality.IntermediateBridgeCoverData.Batch240_255
import ForestUnimodality.ActivityPointDensityData.Point049
import ForestUnimodality.ActivityPointDensityData.Point050
import ForestUnimodality.ActivityPointDensityData.Point051
import ForestUnimodality.ActivityPointDensityData.Point052

namespace ForestUnimodality.IntermediateBridgeRankData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem band240_rank : band240.RankValid := by
  exact band240.rank_of_certificate ActivityPointDensityData.Point049.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point049.checked)
    (1/1) (by decide +kernel)
#print axioms band240_rank

theorem band241_rank : band241.RankValid := by
  exact band241.rank_of_certificate ActivityPointDensityData.Point049.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point049.checked)
    (1/1) (by decide +kernel)
#print axioms band241_rank

theorem band242_rank : band242.RankValid := by
  exact band242.rank_of_certificate ActivityPointDensityData.Point049.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point049.checked)
    (1/1) (by decide +kernel)
#print axioms band242_rank

theorem band243_rank : band243.RankValid := by
  exact band243.rank_of_certificate ActivityPointDensityData.Point049.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point049.checked)
    (1/1) (by decide +kernel)
#print axioms band243_rank

theorem band244_rank : band244.RankValid := by
  exact band244.rank_of_certificate ActivityPointDensityData.Point050.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point050.checked)
    (1/1) (by decide +kernel)
#print axioms band244_rank

theorem band245_rank : band245.RankValid := by
  exact band245.rank_of_certificate ActivityPointDensityData.Point050.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point050.checked)
    (1/1) (by decide +kernel)
#print axioms band245_rank

theorem band246_rank : band246.RankValid := by
  exact band246.rank_of_certificate ActivityPointDensityData.Point050.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point050.checked)
    (1/1) (by decide +kernel)
#print axioms band246_rank

theorem band247_rank : band247.RankValid := by
  exact band247.rank_of_certificate ActivityPointDensityData.Point050.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point050.checked)
    (1/1) (by decide +kernel)
#print axioms band247_rank

theorem band248_rank : band248.RankValid := by
  exact band248.rank_of_certificate ActivityPointDensityData.Point051.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point051.checked)
    (1/1) (by decide +kernel)
#print axioms band248_rank

theorem band249_rank : band249.RankValid := by
  exact band249.rank_of_certificate ActivityPointDensityData.Point051.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point051.checked)
    (1/1) (by decide +kernel)
#print axioms band249_rank

theorem band250_rank : band250.RankValid := by
  exact band250.rank_of_certificate ActivityPointDensityData.Point051.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point051.checked)
    (1/1) (by decide +kernel)
#print axioms band250_rank

theorem band251_rank : band251.RankValid := by
  exact band251.rank_of_certificate ActivityPointDensityData.Point051.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point051.checked)
    (1/1) (by decide +kernel)
#print axioms band251_rank

theorem band252_rank : band252.RankValid := by
  exact band252.rank_of_certificate ActivityPointDensityData.Point052.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point052.checked)
    (1/1) (by decide +kernel)
#print axioms band252_rank

theorem band253_rank : band253.RankValid := by
  exact band253.rank_of_certificate ActivityPointDensityData.Point052.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point052.checked)
    (1/1) (by decide +kernel)
#print axioms band253_rank

theorem band254_rank : band254.RankValid := by
  exact band254.rank_of_certificate ActivityPointDensityData.Point052.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point052.checked)
    (1/1) (by decide +kernel)
#print axioms band254_rank

theorem band255_rank : band255.RankValid := by
  exact band255.rank_of_certificate ActivityPointDensityData.Point052.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point052.checked)
    (1/1) (by decide +kernel)
#print axioms band255_rank

end ForestUnimodality.IntermediateBridgeRankData
