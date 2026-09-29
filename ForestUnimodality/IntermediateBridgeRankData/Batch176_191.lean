import ForestUnimodality.IntermediateBridgeRank
import ForestUnimodality.IntermediateBridgeCoverData.Batch176_191
import ForestUnimodality.ActivityPointDensityData.Point033
import ForestUnimodality.ActivityPointDensityData.Point034
import ForestUnimodality.ActivityPointDensityData.Point035
import ForestUnimodality.ActivityPointDensityData.Point036

namespace ForestUnimodality.IntermediateBridgeRankData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem band176_rank : band176.RankValid := by
  exact band176.rank_of_certificate ActivityPointDensityData.Point033.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point033.checked)
    (1/1) (by decide +kernel)
#print axioms band176_rank

theorem band177_rank : band177.RankValid := by
  exact band177.rank_of_certificate ActivityPointDensityData.Point033.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point033.checked)
    (1/1) (by decide +kernel)
#print axioms band177_rank

theorem band178_rank : band178.RankValid := by
  exact band178.rank_of_certificate ActivityPointDensityData.Point033.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point033.checked)
    (1/1) (by decide +kernel)
#print axioms band178_rank

theorem band179_rank : band179.RankValid := by
  apply band179.rank_of_central
  decide +kernel
#print axioms band179_rank

theorem band180_rank : band180.RankValid := by
  exact band180.rank_of_certificate ActivityPointDensityData.Point034.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point034.checked)
    (1/1) (by decide +kernel)
#print axioms band180_rank

theorem band181_rank : band181.RankValid := by
  exact band181.rank_of_certificate ActivityPointDensityData.Point034.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point034.checked)
    (1/1) (by decide +kernel)
#print axioms band181_rank

theorem band182_rank : band182.RankValid := by
  exact band182.rank_of_certificate ActivityPointDensityData.Point034.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point034.checked)
    (1/1) (by decide +kernel)
#print axioms band182_rank

theorem band183_rank : band183.RankValid := by
  exact band183.rank_of_certificate ActivityPointDensityData.Point034.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point034.checked)
    (1/1) (by decide +kernel)
#print axioms band183_rank

theorem band184_rank : band184.RankValid := by
  exact band184.rank_of_certificate ActivityPointDensityData.Point035.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point035.checked)
    (1/1) (by decide +kernel)
#print axioms band184_rank

theorem band185_rank : band185.RankValid := by
  exact band185.rank_of_certificate ActivityPointDensityData.Point035.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point035.checked)
    (1/1) (by decide +kernel)
#print axioms band185_rank

theorem band186_rank : band186.RankValid := by
  exact band186.rank_of_certificate ActivityPointDensityData.Point035.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point035.checked)
    (1/1) (by decide +kernel)
#print axioms band186_rank

theorem band187_rank : band187.RankValid := by
  exact band187.rank_of_certificate ActivityPointDensityData.Point035.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point035.checked)
    (1/1) (by decide +kernel)
#print axioms band187_rank

theorem band188_rank : band188.RankValid := by
  exact band188.rank_of_certificate ActivityPointDensityData.Point036.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point036.checked)
    (1/1) (by decide +kernel)
#print axioms band188_rank

theorem band189_rank : band189.RankValid := by
  exact band189.rank_of_certificate ActivityPointDensityData.Point036.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point036.checked)
    (1/1) (by decide +kernel)
#print axioms band189_rank

theorem band190_rank : band190.RankValid := by
  exact band190.rank_of_certificate ActivityPointDensityData.Point036.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point036.checked)
    (1/1) (by decide +kernel)
#print axioms band190_rank

theorem band191_rank : band191.RankValid := by
  exact band191.rank_of_certificate ActivityPointDensityData.Point036.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point036.checked)
    (1/1) (by decide +kernel)
#print axioms band191_rank

end ForestUnimodality.IntermediateBridgeRankData
