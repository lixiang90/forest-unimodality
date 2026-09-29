import ForestUnimodality.IntermediateBridgeRank
import ForestUnimodality.IntermediateBridgeCoverData.Batch608_615
import ForestUnimodality.ActivityPointDensityData.Point105

namespace ForestUnimodality.IntermediateBridgeRankData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem band608_rank : band608.RankValid := by
  exact band608.rank_of_certificate ActivityPointDensityData.Point105.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point105.checked)
    (2258786014656766208990430823239844665071/2000000000000000000000000000000000000000) (by decide +kernel)
#print axioms band608_rank

theorem band609_rank : band609.RankValid := by
  exact band609.rank_of_certificate ActivityPointDensityData.Point105.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point105.checked)
    (2258786014656766208990430823239844665071/2000000000000000000000000000000000000000) (by decide +kernel)
#print axioms band609_rank

theorem band610_rank : band610.RankValid := by
  exact band610.rank_of_certificate ActivityPointDensityData.Point105.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point105.checked)
    (2258786014656766208990430823239844665071/2000000000000000000000000000000000000000) (by decide +kernel)
#print axioms band610_rank

theorem band611_rank : band611.RankValid := by
  exact band611.rank_of_certificate ActivityPointDensityData.Point105.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point105.checked)
    (2258786014656766208990430823239844665071/2000000000000000000000000000000000000000) (by decide +kernel)
#print axioms band611_rank

theorem band612_rank : band612.RankValid := by
  exact band612.rank_of_certificate ActivityPointDensityData.Point105.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point105.checked)
    (11347078273068036942532843507670033241861/10000000000000000000000000000000000000000) (by decide +kernel)
#print axioms band612_rank

theorem band613_rank : band613.RankValid := by
  exact band613.rank_of_certificate ActivityPointDensityData.Point105.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point105.checked)
    (11347078273068036942532843507670033241861/10000000000000000000000000000000000000000) (by decide +kernel)
#print axioms band613_rank

theorem band614_rank : band614.RankValid := by
  exact band614.rank_of_certificate ActivityPointDensityData.Point105.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point105.checked)
    (11347078273068036942532843507670033241861/10000000000000000000000000000000000000000) (by decide +kernel)
#print axioms band614_rank

theorem band615_rank : band615.RankValid := by
  exact band615.rank_of_certificate ActivityPointDensityData.Point105.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point105.checked)
    (11347078273068036942532843507670033241861/10000000000000000000000000000000000000000) (by decide +kernel)
#print axioms band615_rank

end ForestUnimodality.IntermediateBridgeRankData
