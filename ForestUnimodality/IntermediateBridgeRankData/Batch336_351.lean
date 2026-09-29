import ForestUnimodality.IntermediateBridgeRank
import ForestUnimodality.IntermediateBridgeCoverData.Batch336_351
import ForestUnimodality.ActivityPointDensityData.Point073
import ForestUnimodality.ActivityPointDensityData.Point074
import ForestUnimodality.ActivityPointDensityData.Point075
import ForestUnimodality.ActivityPointDensityData.Point076

namespace ForestUnimodality.IntermediateBridgeRankData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem band336_rank : band336.RankValid := by
  exact band336.rank_of_certificate ActivityPointDensityData.Point073.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point073.checked)
    (1/1) (by decide +kernel)
#print axioms band336_rank

theorem band337_rank : band337.RankValid := by
  exact band337.rank_of_certificate ActivityPointDensityData.Point073.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point073.checked)
    (1/1) (by decide +kernel)
#print axioms band337_rank

theorem band338_rank : band338.RankValid := by
  exact band338.rank_of_certificate ActivityPointDensityData.Point073.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point073.checked)
    (1/1) (by decide +kernel)
#print axioms band338_rank

theorem band339_rank : band339.RankValid := by
  exact band339.rank_of_certificate ActivityPointDensityData.Point073.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point073.checked)
    (1/1) (by decide +kernel)
#print axioms band339_rank

theorem band340_rank : band340.RankValid := by
  exact band340.rank_of_certificate ActivityPointDensityData.Point074.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point074.checked)
    (1/1) (by decide +kernel)
#print axioms band340_rank

theorem band341_rank : band341.RankValid := by
  exact band341.rank_of_certificate ActivityPointDensityData.Point074.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point074.checked)
    (1/1) (by decide +kernel)
#print axioms band341_rank

theorem band342_rank : band342.RankValid := by
  exact band342.rank_of_certificate ActivityPointDensityData.Point074.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point074.checked)
    (1/1) (by decide +kernel)
#print axioms band342_rank

theorem band343_rank : band343.RankValid := by
  exact band343.rank_of_certificate ActivityPointDensityData.Point074.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point074.checked)
    (1/1) (by decide +kernel)
#print axioms band343_rank

theorem band344_rank : band344.RankValid := by
  exact band344.rank_of_certificate ActivityPointDensityData.Point075.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point075.checked)
    (1/1) (by decide +kernel)
#print axioms band344_rank

theorem band345_rank : band345.RankValid := by
  exact band345.rank_of_certificate ActivityPointDensityData.Point075.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point075.checked)
    (1/1) (by decide +kernel)
#print axioms band345_rank

theorem band346_rank : band346.RankValid := by
  exact band346.rank_of_certificate ActivityPointDensityData.Point075.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point075.checked)
    (1/1) (by decide +kernel)
#print axioms band346_rank

theorem band347_rank : band347.RankValid := by
  exact band347.rank_of_certificate ActivityPointDensityData.Point075.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point075.checked)
    (1/1) (by decide +kernel)
#print axioms band347_rank

theorem band348_rank : band348.RankValid := by
  exact band348.rank_of_certificate ActivityPointDensityData.Point076.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point076.checked)
    (1/1) (by decide +kernel)
#print axioms band348_rank

theorem band349_rank : band349.RankValid := by
  exact band349.rank_of_certificate ActivityPointDensityData.Point076.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point076.checked)
    (1/1) (by decide +kernel)
#print axioms band349_rank

theorem band350_rank : band350.RankValid := by
  exact band350.rank_of_certificate ActivityPointDensityData.Point076.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point076.checked)
    (1/1) (by decide +kernel)
#print axioms band350_rank

theorem band351_rank : band351.RankValid := by
  exact band351.rank_of_certificate ActivityPointDensityData.Point076.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point076.checked)
    (1/1) (by decide +kernel)
#print axioms band351_rank

end ForestUnimodality.IntermediateBridgeRankData
