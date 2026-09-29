import ForestUnimodality.IntermediateBridgeRank
import ForestUnimodality.IntermediateBridgeCoverData.Batch224_239
import ForestUnimodality.ActivityPointDensityData.Point045
import ForestUnimodality.ActivityPointDensityData.Point046
import ForestUnimodality.ActivityPointDensityData.Point047
import ForestUnimodality.ActivityPointDensityData.Point048

namespace ForestUnimodality.IntermediateBridgeRankData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem band224_rank : band224.RankValid := by
  exact band224.rank_of_certificate ActivityPointDensityData.Point045.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point045.checked)
    (1/1) (by decide +kernel)
#print axioms band224_rank

theorem band225_rank : band225.RankValid := by
  exact band225.rank_of_certificate ActivityPointDensityData.Point045.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point045.checked)
    (1/1) (by decide +kernel)
#print axioms band225_rank

theorem band226_rank : band226.RankValid := by
  exact band226.rank_of_certificate ActivityPointDensityData.Point045.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point045.checked)
    (1/1) (by decide +kernel)
#print axioms band226_rank

theorem band227_rank : band227.RankValid := by
  exact band227.rank_of_certificate ActivityPointDensityData.Point045.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point045.checked)
    (1/1) (by decide +kernel)
#print axioms band227_rank

theorem band228_rank : band228.RankValid := by
  exact band228.rank_of_certificate ActivityPointDensityData.Point046.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point046.checked)
    (1/1) (by decide +kernel)
#print axioms band228_rank

theorem band229_rank : band229.RankValid := by
  exact band229.rank_of_certificate ActivityPointDensityData.Point046.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point046.checked)
    (1/1) (by decide +kernel)
#print axioms band229_rank

theorem band230_rank : band230.RankValid := by
  exact band230.rank_of_certificate ActivityPointDensityData.Point046.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point046.checked)
    (1/1) (by decide +kernel)
#print axioms band230_rank

theorem band231_rank : band231.RankValid := by
  exact band231.rank_of_certificate ActivityPointDensityData.Point046.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point046.checked)
    (1/1) (by decide +kernel)
#print axioms band231_rank

theorem band232_rank : band232.RankValid := by
  exact band232.rank_of_certificate ActivityPointDensityData.Point047.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point047.checked)
    (1/1) (by decide +kernel)
#print axioms band232_rank

theorem band233_rank : band233.RankValid := by
  exact band233.rank_of_certificate ActivityPointDensityData.Point047.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point047.checked)
    (1/1) (by decide +kernel)
#print axioms band233_rank

theorem band234_rank : band234.RankValid := by
  exact band234.rank_of_certificate ActivityPointDensityData.Point047.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point047.checked)
    (1/1) (by decide +kernel)
#print axioms band234_rank

theorem band235_rank : band235.RankValid := by
  exact band235.rank_of_certificate ActivityPointDensityData.Point047.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point047.checked)
    (1/1) (by decide +kernel)
#print axioms band235_rank

theorem band236_rank : band236.RankValid := by
  exact band236.rank_of_certificate ActivityPointDensityData.Point048.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point048.checked)
    (1/1) (by decide +kernel)
#print axioms band236_rank

theorem band237_rank : band237.RankValid := by
  exact band237.rank_of_certificate ActivityPointDensityData.Point048.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point048.checked)
    (1/1) (by decide +kernel)
#print axioms band237_rank

theorem band238_rank : band238.RankValid := by
  exact band238.rank_of_certificate ActivityPointDensityData.Point048.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point048.checked)
    (1/1) (by decide +kernel)
#print axioms band238_rank

theorem band239_rank : band239.RankValid := by
  exact band239.rank_of_certificate ActivityPointDensityData.Point048.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point048.checked)
    (1/1) (by decide +kernel)
#print axioms band239_rank

end ForestUnimodality.IntermediateBridgeRankData
