import ForestUnimodality.IntermediateBridgeRank
import ForestUnimodality.IntermediateBridgeCoverData.Batch384_399
import ForestUnimodality.ActivityPointDensityData.Point085
import ForestUnimodality.ActivityPointDensityData.Point086
import ForestUnimodality.ActivityPointDensityData.Point087
import ForestUnimodality.ActivityPointDensityData.Point088

namespace ForestUnimodality.IntermediateBridgeRankData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem band384_rank : band384.RankValid := by
  exact band384.rank_of_certificate ActivityPointDensityData.Point085.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point085.checked)
    (1/1) (by decide +kernel)
#print axioms band384_rank

theorem band385_rank : band385.RankValid := by
  exact band385.rank_of_certificate ActivityPointDensityData.Point085.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point085.checked)
    (1/1) (by decide +kernel)
#print axioms band385_rank

theorem band386_rank : band386.RankValid := by
  exact band386.rank_of_certificate ActivityPointDensityData.Point085.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point085.checked)
    (1/1) (by decide +kernel)
#print axioms band386_rank

theorem band387_rank : band387.RankValid := by
  exact band387.rank_of_certificate ActivityPointDensityData.Point085.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point085.checked)
    (1/1) (by decide +kernel)
#print axioms band387_rank

theorem band388_rank : band388.RankValid := by
  exact band388.rank_of_certificate ActivityPointDensityData.Point086.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point086.checked)
    (1/1) (by decide +kernel)
#print axioms band388_rank

theorem band389_rank : band389.RankValid := by
  exact band389.rank_of_certificate ActivityPointDensityData.Point086.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point086.checked)
    (1/1) (by decide +kernel)
#print axioms band389_rank

theorem band390_rank : band390.RankValid := by
  exact band390.rank_of_certificate ActivityPointDensityData.Point086.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point086.checked)
    (1/1) (by decide +kernel)
#print axioms band390_rank

theorem band391_rank : band391.RankValid := by
  exact band391.rank_of_certificate ActivityPointDensityData.Point086.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point086.checked)
    (1/1) (by decide +kernel)
#print axioms band391_rank

theorem band392_rank : band392.RankValid := by
  exact band392.rank_of_certificate ActivityPointDensityData.Point087.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point087.checked)
    (1/1) (by decide +kernel)
#print axioms band392_rank

theorem band393_rank : band393.RankValid := by
  exact band393.rank_of_certificate ActivityPointDensityData.Point087.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point087.checked)
    (1/1) (by decide +kernel)
#print axioms band393_rank

theorem band394_rank : band394.RankValid := by
  exact band394.rank_of_certificate ActivityPointDensityData.Point087.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point087.checked)
    (1/1) (by decide +kernel)
#print axioms band394_rank

theorem band395_rank : band395.RankValid := by
  exact band395.rank_of_certificate ActivityPointDensityData.Point087.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point087.checked)
    (1/1) (by decide +kernel)
#print axioms band395_rank

theorem band396_rank : band396.RankValid := by
  exact band396.rank_of_certificate ActivityPointDensityData.Point088.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point088.checked)
    (1/1) (by decide +kernel)
#print axioms band396_rank

theorem band397_rank : band397.RankValid := by
  exact band397.rank_of_certificate ActivityPointDensityData.Point088.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point088.checked)
    (1/1) (by decide +kernel)
#print axioms band397_rank

theorem band398_rank : band398.RankValid := by
  exact band398.rank_of_certificate ActivityPointDensityData.Point088.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point088.checked)
    (1/1) (by decide +kernel)
#print axioms band398_rank

theorem band399_rank : band399.RankValid := by
  exact band399.rank_of_certificate ActivityPointDensityData.Point088.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point088.checked)
    (1/1) (by decide +kernel)
#print axioms band399_rank

end ForestUnimodality.IntermediateBridgeRankData
