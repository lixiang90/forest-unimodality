import ForestUnimodality.IntermediateBridgeRank
import ForestUnimodality.IntermediateBridgeCoverData.Batch160_175
import ForestUnimodality.ActivityPointDensityData.Point029
import ForestUnimodality.ActivityPointDensityData.Point030
import ForestUnimodality.ActivityPointDensityData.Point031
import ForestUnimodality.ActivityPointDensityData.Point032

namespace ForestUnimodality.IntermediateBridgeRankData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem band160_rank : band160.RankValid := by
  exact band160.rank_of_certificate ActivityPointDensityData.Point029.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point029.checked)
    (1/1) (by decide +kernel)
#print axioms band160_rank

theorem band161_rank : band161.RankValid := by
  exact band161.rank_of_certificate ActivityPointDensityData.Point029.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point029.checked)
    (1/1) (by decide +kernel)
#print axioms band161_rank

theorem band162_rank : band162.RankValid := by
  exact band162.rank_of_certificate ActivityPointDensityData.Point029.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point029.checked)
    (1/1) (by decide +kernel)
#print axioms band162_rank

theorem band163_rank : band163.RankValid := by
  apply band163.rank_of_central
  decide +kernel
#print axioms band163_rank

theorem band164_rank : band164.RankValid := by
  exact band164.rank_of_certificate ActivityPointDensityData.Point030.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point030.checked)
    (1/1) (by decide +kernel)
#print axioms band164_rank

theorem band165_rank : band165.RankValid := by
  exact band165.rank_of_certificate ActivityPointDensityData.Point030.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point030.checked)
    (1/1) (by decide +kernel)
#print axioms band165_rank

theorem band166_rank : band166.RankValid := by
  exact band166.rank_of_certificate ActivityPointDensityData.Point030.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point030.checked)
    (1/1) (by decide +kernel)
#print axioms band166_rank

theorem band167_rank : band167.RankValid := by
  apply band167.rank_of_central
  decide +kernel
#print axioms band167_rank

theorem band168_rank : band168.RankValid := by
  exact band168.rank_of_certificate ActivityPointDensityData.Point031.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point031.checked)
    (1/1) (by decide +kernel)
#print axioms band168_rank

theorem band169_rank : band169.RankValid := by
  exact band169.rank_of_certificate ActivityPointDensityData.Point031.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point031.checked)
    (1/1) (by decide +kernel)
#print axioms band169_rank

theorem band170_rank : band170.RankValid := by
  exact band170.rank_of_certificate ActivityPointDensityData.Point031.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point031.checked)
    (1/1) (by decide +kernel)
#print axioms band170_rank

theorem band171_rank : band171.RankValid := by
  apply band171.rank_of_central
  decide +kernel
#print axioms band171_rank

theorem band172_rank : band172.RankValid := by
  exact band172.rank_of_certificate ActivityPointDensityData.Point032.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point032.checked)
    (1/1) (by decide +kernel)
#print axioms band172_rank

theorem band173_rank : band173.RankValid := by
  exact band173.rank_of_certificate ActivityPointDensityData.Point032.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point032.checked)
    (1/1) (by decide +kernel)
#print axioms band173_rank

theorem band174_rank : band174.RankValid := by
  exact band174.rank_of_certificate ActivityPointDensityData.Point032.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point032.checked)
    (1/1) (by decide +kernel)
#print axioms band174_rank

theorem band175_rank : band175.RankValid := by
  apply band175.rank_of_central
  decide +kernel
#print axioms band175_rank

end ForestUnimodality.IntermediateBridgeRankData
