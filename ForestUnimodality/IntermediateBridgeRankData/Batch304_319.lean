import ForestUnimodality.IntermediateBridgeRank
import ForestUnimodality.IntermediateBridgeCoverData.Batch304_319
import ForestUnimodality.ActivityPointDensityData.Point065
import ForestUnimodality.ActivityPointDensityData.Point066
import ForestUnimodality.ActivityPointDensityData.Point067
import ForestUnimodality.ActivityPointDensityData.Point068

namespace ForestUnimodality.IntermediateBridgeRankData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem band304_rank : band304.RankValid := by
  exact band304.rank_of_certificate ActivityPointDensityData.Point065.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point065.checked)
    (1/1) (by decide +kernel)
#print axioms band304_rank

theorem band305_rank : band305.RankValid := by
  exact band305.rank_of_certificate ActivityPointDensityData.Point065.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point065.checked)
    (1/1) (by decide +kernel)
#print axioms band305_rank

theorem band306_rank : band306.RankValid := by
  exact band306.rank_of_certificate ActivityPointDensityData.Point065.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point065.checked)
    (1/1) (by decide +kernel)
#print axioms band306_rank

theorem band307_rank : band307.RankValid := by
  exact band307.rank_of_certificate ActivityPointDensityData.Point065.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point065.checked)
    (1/1) (by decide +kernel)
#print axioms band307_rank

theorem band308_rank : band308.RankValid := by
  exact band308.rank_of_certificate ActivityPointDensityData.Point066.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point066.checked)
    (1/1) (by decide +kernel)
#print axioms band308_rank

theorem band309_rank : band309.RankValid := by
  exact band309.rank_of_certificate ActivityPointDensityData.Point066.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point066.checked)
    (1/1) (by decide +kernel)
#print axioms band309_rank

theorem band310_rank : band310.RankValid := by
  exact band310.rank_of_certificate ActivityPointDensityData.Point066.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point066.checked)
    (1/1) (by decide +kernel)
#print axioms band310_rank

theorem band311_rank : band311.RankValid := by
  exact band311.rank_of_certificate ActivityPointDensityData.Point066.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point066.checked)
    (1/1) (by decide +kernel)
#print axioms band311_rank

theorem band312_rank : band312.RankValid := by
  exact band312.rank_of_certificate ActivityPointDensityData.Point067.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point067.checked)
    (1/1) (by decide +kernel)
#print axioms band312_rank

theorem band313_rank : band313.RankValid := by
  exact band313.rank_of_certificate ActivityPointDensityData.Point067.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point067.checked)
    (1/1) (by decide +kernel)
#print axioms band313_rank

theorem band314_rank : band314.RankValid := by
  exact band314.rank_of_certificate ActivityPointDensityData.Point067.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point067.checked)
    (1/1) (by decide +kernel)
#print axioms band314_rank

theorem band315_rank : band315.RankValid := by
  exact band315.rank_of_certificate ActivityPointDensityData.Point067.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point067.checked)
    (1/1) (by decide +kernel)
#print axioms band315_rank

theorem band316_rank : band316.RankValid := by
  exact band316.rank_of_certificate ActivityPointDensityData.Point068.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point068.checked)
    (1/1) (by decide +kernel)
#print axioms band316_rank

theorem band317_rank : band317.RankValid := by
  exact band317.rank_of_certificate ActivityPointDensityData.Point068.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point068.checked)
    (1/1) (by decide +kernel)
#print axioms band317_rank

theorem band318_rank : band318.RankValid := by
  exact band318.rank_of_certificate ActivityPointDensityData.Point068.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point068.checked)
    (1/1) (by decide +kernel)
#print axioms band318_rank

theorem band319_rank : band319.RankValid := by
  exact band319.rank_of_certificate ActivityPointDensityData.Point068.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point068.checked)
    (1/1) (by decide +kernel)
#print axioms band319_rank

end ForestUnimodality.IntermediateBridgeRankData
