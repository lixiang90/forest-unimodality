import ForestUnimodality.IntermediateBridgeRank
import ForestUnimodality.IntermediateBridgeCoverData.Batch320_335
import ForestUnimodality.ActivityPointDensityData.Point069
import ForestUnimodality.ActivityPointDensityData.Point070
import ForestUnimodality.ActivityPointDensityData.Point071
import ForestUnimodality.ActivityPointDensityData.Point072

namespace ForestUnimodality.IntermediateBridgeRankData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem band320_rank : band320.RankValid := by
  exact band320.rank_of_certificate ActivityPointDensityData.Point069.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point069.checked)
    (1/1) (by decide +kernel)
#print axioms band320_rank

theorem band321_rank : band321.RankValid := by
  exact band321.rank_of_certificate ActivityPointDensityData.Point069.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point069.checked)
    (1/1) (by decide +kernel)
#print axioms band321_rank

theorem band322_rank : band322.RankValid := by
  exact band322.rank_of_certificate ActivityPointDensityData.Point069.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point069.checked)
    (1/1) (by decide +kernel)
#print axioms band322_rank

theorem band323_rank : band323.RankValid := by
  exact band323.rank_of_certificate ActivityPointDensityData.Point069.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point069.checked)
    (1/1) (by decide +kernel)
#print axioms band323_rank

theorem band324_rank : band324.RankValid := by
  exact band324.rank_of_certificate ActivityPointDensityData.Point070.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point070.checked)
    (1/1) (by decide +kernel)
#print axioms band324_rank

theorem band325_rank : band325.RankValid := by
  exact band325.rank_of_certificate ActivityPointDensityData.Point070.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point070.checked)
    (1/1) (by decide +kernel)
#print axioms band325_rank

theorem band326_rank : band326.RankValid := by
  exact band326.rank_of_certificate ActivityPointDensityData.Point070.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point070.checked)
    (1/1) (by decide +kernel)
#print axioms band326_rank

theorem band327_rank : band327.RankValid := by
  exact band327.rank_of_certificate ActivityPointDensityData.Point070.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point070.checked)
    (1/1) (by decide +kernel)
#print axioms band327_rank

theorem band328_rank : band328.RankValid := by
  exact band328.rank_of_certificate ActivityPointDensityData.Point071.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point071.checked)
    (1/1) (by decide +kernel)
#print axioms band328_rank

theorem band329_rank : band329.RankValid := by
  exact band329.rank_of_certificate ActivityPointDensityData.Point071.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point071.checked)
    (1/1) (by decide +kernel)
#print axioms band329_rank

theorem band330_rank : band330.RankValid := by
  exact band330.rank_of_certificate ActivityPointDensityData.Point071.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point071.checked)
    (1/1) (by decide +kernel)
#print axioms band330_rank

theorem band331_rank : band331.RankValid := by
  exact band331.rank_of_certificate ActivityPointDensityData.Point071.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point071.checked)
    (1/1) (by decide +kernel)
#print axioms band331_rank

theorem band332_rank : band332.RankValid := by
  exact band332.rank_of_certificate ActivityPointDensityData.Point072.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point072.checked)
    (1/1) (by decide +kernel)
#print axioms band332_rank

theorem band333_rank : band333.RankValid := by
  exact band333.rank_of_certificate ActivityPointDensityData.Point072.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point072.checked)
    (1/1) (by decide +kernel)
#print axioms band333_rank

theorem band334_rank : band334.RankValid := by
  exact band334.rank_of_certificate ActivityPointDensityData.Point072.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point072.checked)
    (1/1) (by decide +kernel)
#print axioms band334_rank

theorem band335_rank : band335.RankValid := by
  exact band335.rank_of_certificate ActivityPointDensityData.Point072.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point072.checked)
    (1/1) (by decide +kernel)
#print axioms band335_rank

end ForestUnimodality.IntermediateBridgeRankData
