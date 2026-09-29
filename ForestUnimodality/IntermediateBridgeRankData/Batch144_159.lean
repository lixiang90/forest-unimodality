import ForestUnimodality.IntermediateBridgeRank
import ForestUnimodality.IntermediateBridgeCoverData.Batch144_159
import ForestUnimodality.ActivityPointDensityData.Point025
import ForestUnimodality.ActivityPointDensityData.Point026
import ForestUnimodality.ActivityPointDensityData.Point027
import ForestUnimodality.ActivityPointDensityData.Point028

namespace ForestUnimodality.IntermediateBridgeRankData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem band144_rank : band144.RankValid := by
  exact band144.rank_of_certificate ActivityPointDensityData.Point025.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point025.checked)
    (1/1) (by decide +kernel)
#print axioms band144_rank

theorem band145_rank : band145.RankValid := by
  exact band145.rank_of_certificate ActivityPointDensityData.Point025.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point025.checked)
    (1/1) (by decide +kernel)
#print axioms band145_rank

theorem band146_rank : band146.RankValid := by
  exact band146.rank_of_certificate ActivityPointDensityData.Point025.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point025.checked)
    (1/1) (by decide +kernel)
#print axioms band146_rank

theorem band147_rank : band147.RankValid := by
  apply band147.rank_of_central
  decide +kernel
#print axioms band147_rank

theorem band148_rank : band148.RankValid := by
  exact band148.rank_of_certificate ActivityPointDensityData.Point026.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point026.checked)
    (1/1) (by decide +kernel)
#print axioms band148_rank

theorem band149_rank : band149.RankValid := by
  exact band149.rank_of_certificate ActivityPointDensityData.Point026.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point026.checked)
    (1/1) (by decide +kernel)
#print axioms band149_rank

theorem band150_rank : band150.RankValid := by
  exact band150.rank_of_certificate ActivityPointDensityData.Point026.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point026.checked)
    (1/1) (by decide +kernel)
#print axioms band150_rank

theorem band151_rank : band151.RankValid := by
  apply band151.rank_of_central
  decide +kernel
#print axioms band151_rank

theorem band152_rank : band152.RankValid := by
  exact band152.rank_of_certificate ActivityPointDensityData.Point027.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point027.checked)
    (1/1) (by decide +kernel)
#print axioms band152_rank

theorem band153_rank : band153.RankValid := by
  exact band153.rank_of_certificate ActivityPointDensityData.Point027.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point027.checked)
    (1/1) (by decide +kernel)
#print axioms band153_rank

theorem band154_rank : band154.RankValid := by
  exact band154.rank_of_certificate ActivityPointDensityData.Point027.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point027.checked)
    (1/1) (by decide +kernel)
#print axioms band154_rank

theorem band155_rank : band155.RankValid := by
  apply band155.rank_of_central
  decide +kernel
#print axioms band155_rank

theorem band156_rank : band156.RankValid := by
  exact band156.rank_of_certificate ActivityPointDensityData.Point028.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point028.checked)
    (1/1) (by decide +kernel)
#print axioms band156_rank

theorem band157_rank : band157.RankValid := by
  exact band157.rank_of_certificate ActivityPointDensityData.Point028.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point028.checked)
    (1/1) (by decide +kernel)
#print axioms band157_rank

theorem band158_rank : band158.RankValid := by
  exact band158.rank_of_certificate ActivityPointDensityData.Point028.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point028.checked)
    (1/1) (by decide +kernel)
#print axioms band158_rank

theorem band159_rank : band159.RankValid := by
  apply band159.rank_of_central
  decide +kernel
#print axioms band159_rank

end ForestUnimodality.IntermediateBridgeRankData
