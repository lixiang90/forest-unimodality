import ForestUnimodality.IntermediateBridgeRank
import ForestUnimodality.IntermediateBridgeCoverData.Batch368_383
import ForestUnimodality.ActivityPointDensityData.Point081
import ForestUnimodality.ActivityPointDensityData.Point082
import ForestUnimodality.ActivityPointDensityData.Point083
import ForestUnimodality.ActivityPointDensityData.Point084

namespace ForestUnimodality.IntermediateBridgeRankData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem band368_rank : band368.RankValid := by
  exact band368.rank_of_certificate ActivityPointDensityData.Point081.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point081.checked)
    (1/1) (by decide +kernel)
#print axioms band368_rank

theorem band369_rank : band369.RankValid := by
  exact band369.rank_of_certificate ActivityPointDensityData.Point081.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point081.checked)
    (1/1) (by decide +kernel)
#print axioms band369_rank

theorem band370_rank : band370.RankValid := by
  exact band370.rank_of_certificate ActivityPointDensityData.Point081.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point081.checked)
    (1/1) (by decide +kernel)
#print axioms band370_rank

theorem band371_rank : band371.RankValid := by
  exact band371.rank_of_certificate ActivityPointDensityData.Point081.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point081.checked)
    (1/1) (by decide +kernel)
#print axioms band371_rank

theorem band372_rank : band372.RankValid := by
  exact band372.rank_of_certificate ActivityPointDensityData.Point082.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point082.checked)
    (1/1) (by decide +kernel)
#print axioms band372_rank

theorem band373_rank : band373.RankValid := by
  exact band373.rank_of_certificate ActivityPointDensityData.Point082.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point082.checked)
    (1/1) (by decide +kernel)
#print axioms band373_rank

theorem band374_rank : band374.RankValid := by
  exact band374.rank_of_certificate ActivityPointDensityData.Point082.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point082.checked)
    (1/1) (by decide +kernel)
#print axioms band374_rank

theorem band375_rank : band375.RankValid := by
  exact band375.rank_of_certificate ActivityPointDensityData.Point082.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point082.checked)
    (1/1) (by decide +kernel)
#print axioms band375_rank

theorem band376_rank : band376.RankValid := by
  exact band376.rank_of_certificate ActivityPointDensityData.Point083.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point083.checked)
    (1/1) (by decide +kernel)
#print axioms band376_rank

theorem band377_rank : band377.RankValid := by
  exact band377.rank_of_certificate ActivityPointDensityData.Point083.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point083.checked)
    (1/1) (by decide +kernel)
#print axioms band377_rank

theorem band378_rank : band378.RankValid := by
  exact band378.rank_of_certificate ActivityPointDensityData.Point083.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point083.checked)
    (1/1) (by decide +kernel)
#print axioms band378_rank

theorem band379_rank : band379.RankValid := by
  exact band379.rank_of_certificate ActivityPointDensityData.Point083.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point083.checked)
    (1/1) (by decide +kernel)
#print axioms band379_rank

theorem band380_rank : band380.RankValid := by
  exact band380.rank_of_certificate ActivityPointDensityData.Point084.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point084.checked)
    (1/1) (by decide +kernel)
#print axioms band380_rank

theorem band381_rank : band381.RankValid := by
  exact band381.rank_of_certificate ActivityPointDensityData.Point084.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point084.checked)
    (1/1) (by decide +kernel)
#print axioms band381_rank

theorem band382_rank : band382.RankValid := by
  exact band382.rank_of_certificate ActivityPointDensityData.Point084.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point084.checked)
    (1/1) (by decide +kernel)
#print axioms band382_rank

theorem band383_rank : band383.RankValid := by
  exact band383.rank_of_certificate ActivityPointDensityData.Point084.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point084.checked)
    (1/1) (by decide +kernel)
#print axioms band383_rank

end ForestUnimodality.IntermediateBridgeRankData
