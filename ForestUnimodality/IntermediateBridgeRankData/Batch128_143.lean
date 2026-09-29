import ForestUnimodality.IntermediateBridgeRank
import ForestUnimodality.IntermediateBridgeCoverData.Batch128_143
import ForestUnimodality.ActivityPointDensityData.Point021
import ForestUnimodality.ActivityPointDensityData.Point022
import ForestUnimodality.ActivityPointDensityData.Point023
import ForestUnimodality.ActivityPointDensityData.Point024

namespace ForestUnimodality.IntermediateBridgeRankData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem band128_rank : band128.RankValid := by
  exact band128.rank_of_certificate ActivityPointDensityData.Point021.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point021.checked)
    (1/1) (by decide +kernel)
#print axioms band128_rank

theorem band129_rank : band129.RankValid := by
  exact band129.rank_of_certificate ActivityPointDensityData.Point021.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point021.checked)
    (1/1) (by decide +kernel)
#print axioms band129_rank

theorem band130_rank : band130.RankValid := by
  exact band130.rank_of_certificate ActivityPointDensityData.Point021.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point021.checked)
    (1/1) (by decide +kernel)
#print axioms band130_rank

theorem band131_rank : band131.RankValid := by
  apply band131.rank_of_central
  decide +kernel
#print axioms band131_rank

theorem band132_rank : band132.RankValid := by
  exact band132.rank_of_certificate ActivityPointDensityData.Point022.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point022.checked)
    (1/1) (by decide +kernel)
#print axioms band132_rank

theorem band133_rank : band133.RankValid := by
  exact band133.rank_of_certificate ActivityPointDensityData.Point022.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point022.checked)
    (1/1) (by decide +kernel)
#print axioms band133_rank

theorem band134_rank : band134.RankValid := by
  exact band134.rank_of_certificate ActivityPointDensityData.Point022.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point022.checked)
    (1/1) (by decide +kernel)
#print axioms band134_rank

theorem band135_rank : band135.RankValid := by
  apply band135.rank_of_central
  decide +kernel
#print axioms band135_rank

theorem band136_rank : band136.RankValid := by
  exact band136.rank_of_certificate ActivityPointDensityData.Point023.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point023.checked)
    (1/1) (by decide +kernel)
#print axioms band136_rank

theorem band137_rank : band137.RankValid := by
  exact band137.rank_of_certificate ActivityPointDensityData.Point023.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point023.checked)
    (1/1) (by decide +kernel)
#print axioms band137_rank

theorem band138_rank : band138.RankValid := by
  exact band138.rank_of_certificate ActivityPointDensityData.Point023.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point023.checked)
    (1/1) (by decide +kernel)
#print axioms band138_rank

theorem band139_rank : band139.RankValid := by
  apply band139.rank_of_central
  decide +kernel
#print axioms band139_rank

theorem band140_rank : band140.RankValid := by
  exact band140.rank_of_certificate ActivityPointDensityData.Point024.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point024.checked)
    (1/1) (by decide +kernel)
#print axioms band140_rank

theorem band141_rank : band141.RankValid := by
  exact band141.rank_of_certificate ActivityPointDensityData.Point024.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point024.checked)
    (1/1) (by decide +kernel)
#print axioms band141_rank

theorem band142_rank : band142.RankValid := by
  exact band142.rank_of_certificate ActivityPointDensityData.Point024.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point024.checked)
    (1/1) (by decide +kernel)
#print axioms band142_rank

theorem band143_rank : band143.RankValid := by
  apply band143.rank_of_central
  decide +kernel
#print axioms band143_rank

end ForestUnimodality.IntermediateBridgeRankData
