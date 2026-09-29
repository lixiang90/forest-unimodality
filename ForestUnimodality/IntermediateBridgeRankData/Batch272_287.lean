import ForestUnimodality.IntermediateBridgeRank
import ForestUnimodality.IntermediateBridgeCoverData.Batch272_287
import ForestUnimodality.ActivityPointDensityData.Point057
import ForestUnimodality.ActivityPointDensityData.Point058
import ForestUnimodality.ActivityPointDensityData.Point059
import ForestUnimodality.ActivityPointDensityData.Point060

namespace ForestUnimodality.IntermediateBridgeRankData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem band272_rank : band272.RankValid := by
  exact band272.rank_of_certificate ActivityPointDensityData.Point057.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point057.checked)
    (1/1) (by decide +kernel)
#print axioms band272_rank

theorem band273_rank : band273.RankValid := by
  exact band273.rank_of_certificate ActivityPointDensityData.Point057.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point057.checked)
    (1/1) (by decide +kernel)
#print axioms band273_rank

theorem band274_rank : band274.RankValid := by
  exact band274.rank_of_certificate ActivityPointDensityData.Point057.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point057.checked)
    (1/1) (by decide +kernel)
#print axioms band274_rank

theorem band275_rank : band275.RankValid := by
  exact band275.rank_of_certificate ActivityPointDensityData.Point057.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point057.checked)
    (1/1) (by decide +kernel)
#print axioms band275_rank

theorem band276_rank : band276.RankValid := by
  exact band276.rank_of_certificate ActivityPointDensityData.Point058.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point058.checked)
    (1/1) (by decide +kernel)
#print axioms band276_rank

theorem band277_rank : band277.RankValid := by
  exact band277.rank_of_certificate ActivityPointDensityData.Point058.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point058.checked)
    (1/1) (by decide +kernel)
#print axioms band277_rank

theorem band278_rank : band278.RankValid := by
  exact band278.rank_of_certificate ActivityPointDensityData.Point058.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point058.checked)
    (1/1) (by decide +kernel)
#print axioms band278_rank

theorem band279_rank : band279.RankValid := by
  exact band279.rank_of_certificate ActivityPointDensityData.Point058.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point058.checked)
    (1/1) (by decide +kernel)
#print axioms band279_rank

theorem band280_rank : band280.RankValid := by
  exact band280.rank_of_certificate ActivityPointDensityData.Point059.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point059.checked)
    (1/1) (by decide +kernel)
#print axioms band280_rank

theorem band281_rank : band281.RankValid := by
  exact band281.rank_of_certificate ActivityPointDensityData.Point059.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point059.checked)
    (1/1) (by decide +kernel)
#print axioms band281_rank

theorem band282_rank : band282.RankValid := by
  exact band282.rank_of_certificate ActivityPointDensityData.Point059.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point059.checked)
    (1/1) (by decide +kernel)
#print axioms band282_rank

theorem band283_rank : band283.RankValid := by
  exact band283.rank_of_certificate ActivityPointDensityData.Point059.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point059.checked)
    (1/1) (by decide +kernel)
#print axioms band283_rank

theorem band284_rank : band284.RankValid := by
  exact band284.rank_of_certificate ActivityPointDensityData.Point060.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point060.checked)
    (1/1) (by decide +kernel)
#print axioms band284_rank

theorem band285_rank : band285.RankValid := by
  exact band285.rank_of_certificate ActivityPointDensityData.Point060.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point060.checked)
    (1/1) (by decide +kernel)
#print axioms band285_rank

theorem band286_rank : band286.RankValid := by
  exact band286.rank_of_certificate ActivityPointDensityData.Point060.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point060.checked)
    (1/1) (by decide +kernel)
#print axioms band286_rank

theorem band287_rank : band287.RankValid := by
  exact band287.rank_of_certificate ActivityPointDensityData.Point060.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point060.checked)
    (1/1) (by decide +kernel)
#print axioms band287_rank

end ForestUnimodality.IntermediateBridgeRankData
