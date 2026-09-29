import ForestUnimodality.IntermediateBridgeRank
import ForestUnimodality.IntermediateBridgeCoverData.Batch192_207
import ForestUnimodality.ActivityPointDensityData.Point037
import ForestUnimodality.ActivityPointDensityData.Point038
import ForestUnimodality.ActivityPointDensityData.Point039
import ForestUnimodality.ActivityPointDensityData.Point040

namespace ForestUnimodality.IntermediateBridgeRankData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem band192_rank : band192.RankValid := by
  exact band192.rank_of_certificate ActivityPointDensityData.Point037.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point037.checked)
    (1/1) (by decide +kernel)
#print axioms band192_rank

theorem band193_rank : band193.RankValid := by
  exact band193.rank_of_certificate ActivityPointDensityData.Point037.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point037.checked)
    (1/1) (by decide +kernel)
#print axioms band193_rank

theorem band194_rank : band194.RankValid := by
  exact band194.rank_of_certificate ActivityPointDensityData.Point037.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point037.checked)
    (1/1) (by decide +kernel)
#print axioms band194_rank

theorem band195_rank : band195.RankValid := by
  exact band195.rank_of_certificate ActivityPointDensityData.Point037.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point037.checked)
    (1/1) (by decide +kernel)
#print axioms band195_rank

theorem band196_rank : band196.RankValid := by
  exact band196.rank_of_certificate ActivityPointDensityData.Point038.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point038.checked)
    (1/1) (by decide +kernel)
#print axioms band196_rank

theorem band197_rank : band197.RankValid := by
  exact band197.rank_of_certificate ActivityPointDensityData.Point038.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point038.checked)
    (1/1) (by decide +kernel)
#print axioms band197_rank

theorem band198_rank : band198.RankValid := by
  exact band198.rank_of_certificate ActivityPointDensityData.Point038.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point038.checked)
    (1/1) (by decide +kernel)
#print axioms band198_rank

theorem band199_rank : band199.RankValid := by
  exact band199.rank_of_certificate ActivityPointDensityData.Point038.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point038.checked)
    (1/1) (by decide +kernel)
#print axioms band199_rank

theorem band200_rank : band200.RankValid := by
  exact band200.rank_of_certificate ActivityPointDensityData.Point039.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point039.checked)
    (1/1) (by decide +kernel)
#print axioms band200_rank

theorem band201_rank : band201.RankValid := by
  exact band201.rank_of_certificate ActivityPointDensityData.Point039.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point039.checked)
    (1/1) (by decide +kernel)
#print axioms band201_rank

theorem band202_rank : band202.RankValid := by
  exact band202.rank_of_certificate ActivityPointDensityData.Point039.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point039.checked)
    (1/1) (by decide +kernel)
#print axioms band202_rank

theorem band203_rank : band203.RankValid := by
  exact band203.rank_of_certificate ActivityPointDensityData.Point039.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point039.checked)
    (1/1) (by decide +kernel)
#print axioms band203_rank

theorem band204_rank : band204.RankValid := by
  exact band204.rank_of_certificate ActivityPointDensityData.Point040.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point040.checked)
    (1/1) (by decide +kernel)
#print axioms band204_rank

theorem band205_rank : band205.RankValid := by
  exact band205.rank_of_certificate ActivityPointDensityData.Point040.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point040.checked)
    (1/1) (by decide +kernel)
#print axioms band205_rank

theorem band206_rank : band206.RankValid := by
  exact band206.rank_of_certificate ActivityPointDensityData.Point040.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point040.checked)
    (1/1) (by decide +kernel)
#print axioms band206_rank

theorem band207_rank : band207.RankValid := by
  exact band207.rank_of_certificate ActivityPointDensityData.Point040.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point040.checked)
    (1/1) (by decide +kernel)
#print axioms band207_rank

end ForestUnimodality.IntermediateBridgeRankData
