import ForestUnimodality.IntermediateBridgeRank
import ForestUnimodality.IntermediateBridgeCoverData.Batch256_271
import ForestUnimodality.ActivityPointDensityData.Point053
import ForestUnimodality.ActivityPointDensityData.Point054
import ForestUnimodality.ActivityPointDensityData.Point055
import ForestUnimodality.ActivityPointDensityData.Point056

namespace ForestUnimodality.IntermediateBridgeRankData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem band256_rank : band256.RankValid := by
  exact band256.rank_of_certificate ActivityPointDensityData.Point053.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point053.checked)
    (1/1) (by decide +kernel)
#print axioms band256_rank

theorem band257_rank : band257.RankValid := by
  exact band257.rank_of_certificate ActivityPointDensityData.Point053.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point053.checked)
    (1/1) (by decide +kernel)
#print axioms band257_rank

theorem band258_rank : band258.RankValid := by
  exact band258.rank_of_certificate ActivityPointDensityData.Point053.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point053.checked)
    (1/1) (by decide +kernel)
#print axioms band258_rank

theorem band259_rank : band259.RankValid := by
  exact band259.rank_of_certificate ActivityPointDensityData.Point053.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point053.checked)
    (1/1) (by decide +kernel)
#print axioms band259_rank

theorem band260_rank : band260.RankValid := by
  exact band260.rank_of_certificate ActivityPointDensityData.Point054.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point054.checked)
    (1/1) (by decide +kernel)
#print axioms band260_rank

theorem band261_rank : band261.RankValid := by
  exact band261.rank_of_certificate ActivityPointDensityData.Point054.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point054.checked)
    (1/1) (by decide +kernel)
#print axioms band261_rank

theorem band262_rank : band262.RankValid := by
  exact band262.rank_of_certificate ActivityPointDensityData.Point054.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point054.checked)
    (1/1) (by decide +kernel)
#print axioms band262_rank

theorem band263_rank : band263.RankValid := by
  exact band263.rank_of_certificate ActivityPointDensityData.Point054.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point054.checked)
    (1/1) (by decide +kernel)
#print axioms band263_rank

theorem band264_rank : band264.RankValid := by
  exact band264.rank_of_certificate ActivityPointDensityData.Point055.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point055.checked)
    (1/1) (by decide +kernel)
#print axioms band264_rank

theorem band265_rank : band265.RankValid := by
  exact band265.rank_of_certificate ActivityPointDensityData.Point055.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point055.checked)
    (1/1) (by decide +kernel)
#print axioms band265_rank

theorem band266_rank : band266.RankValid := by
  exact band266.rank_of_certificate ActivityPointDensityData.Point055.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point055.checked)
    (1/1) (by decide +kernel)
#print axioms band266_rank

theorem band267_rank : band267.RankValid := by
  exact band267.rank_of_certificate ActivityPointDensityData.Point055.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point055.checked)
    (1/1) (by decide +kernel)
#print axioms band267_rank

theorem band268_rank : band268.RankValid := by
  exact band268.rank_of_certificate ActivityPointDensityData.Point056.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point056.checked)
    (1/1) (by decide +kernel)
#print axioms band268_rank

theorem band269_rank : band269.RankValid := by
  exact band269.rank_of_certificate ActivityPointDensityData.Point056.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point056.checked)
    (1/1) (by decide +kernel)
#print axioms band269_rank

theorem band270_rank : band270.RankValid := by
  exact band270.rank_of_certificate ActivityPointDensityData.Point056.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point056.checked)
    (1/1) (by decide +kernel)
#print axioms band270_rank

theorem band271_rank : band271.RankValid := by
  exact band271.rank_of_certificate ActivityPointDensityData.Point056.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point056.checked)
    (1/1) (by decide +kernel)
#print axioms band271_rank

end ForestUnimodality.IntermediateBridgeRankData
