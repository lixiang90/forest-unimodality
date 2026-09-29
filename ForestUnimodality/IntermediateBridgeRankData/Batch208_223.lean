import ForestUnimodality.IntermediateBridgeRank
import ForestUnimodality.IntermediateBridgeCoverData.Batch208_223
import ForestUnimodality.ActivityPointDensityData.Point041
import ForestUnimodality.ActivityPointDensityData.Point042
import ForestUnimodality.ActivityPointDensityData.Point043
import ForestUnimodality.ActivityPointDensityData.Point044

namespace ForestUnimodality.IntermediateBridgeRankData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem band208_rank : band208.RankValid := by
  exact band208.rank_of_certificate ActivityPointDensityData.Point041.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point041.checked)
    (1/1) (by decide +kernel)
#print axioms band208_rank

theorem band209_rank : band209.RankValid := by
  exact band209.rank_of_certificate ActivityPointDensityData.Point041.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point041.checked)
    (1/1) (by decide +kernel)
#print axioms band209_rank

theorem band210_rank : band210.RankValid := by
  exact band210.rank_of_certificate ActivityPointDensityData.Point041.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point041.checked)
    (1/1) (by decide +kernel)
#print axioms band210_rank

theorem band211_rank : band211.RankValid := by
  exact band211.rank_of_certificate ActivityPointDensityData.Point041.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point041.checked)
    (1/1) (by decide +kernel)
#print axioms band211_rank

theorem band212_rank : band212.RankValid := by
  exact band212.rank_of_certificate ActivityPointDensityData.Point042.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point042.checked)
    (1/1) (by decide +kernel)
#print axioms band212_rank

theorem band213_rank : band213.RankValid := by
  exact band213.rank_of_certificate ActivityPointDensityData.Point042.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point042.checked)
    (1/1) (by decide +kernel)
#print axioms band213_rank

theorem band214_rank : band214.RankValid := by
  exact band214.rank_of_certificate ActivityPointDensityData.Point042.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point042.checked)
    (1/1) (by decide +kernel)
#print axioms band214_rank

theorem band215_rank : band215.RankValid := by
  exact band215.rank_of_certificate ActivityPointDensityData.Point042.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point042.checked)
    (1/1) (by decide +kernel)
#print axioms band215_rank

theorem band216_rank : band216.RankValid := by
  exact band216.rank_of_certificate ActivityPointDensityData.Point043.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point043.checked)
    (1/1) (by decide +kernel)
#print axioms band216_rank

theorem band217_rank : band217.RankValid := by
  exact band217.rank_of_certificate ActivityPointDensityData.Point043.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point043.checked)
    (1/1) (by decide +kernel)
#print axioms band217_rank

theorem band218_rank : band218.RankValid := by
  exact band218.rank_of_certificate ActivityPointDensityData.Point043.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point043.checked)
    (1/1) (by decide +kernel)
#print axioms band218_rank

theorem band219_rank : band219.RankValid := by
  exact band219.rank_of_certificate ActivityPointDensityData.Point043.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point043.checked)
    (1/1) (by decide +kernel)
#print axioms band219_rank

theorem band220_rank : band220.RankValid := by
  exact band220.rank_of_certificate ActivityPointDensityData.Point044.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point044.checked)
    (1/1) (by decide +kernel)
#print axioms band220_rank

theorem band221_rank : band221.RankValid := by
  exact band221.rank_of_certificate ActivityPointDensityData.Point044.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point044.checked)
    (1/1) (by decide +kernel)
#print axioms band221_rank

theorem band222_rank : band222.RankValid := by
  exact band222.rank_of_certificate ActivityPointDensityData.Point044.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point044.checked)
    (1/1) (by decide +kernel)
#print axioms band222_rank

theorem band223_rank : band223.RankValid := by
  exact band223.rank_of_certificate ActivityPointDensityData.Point044.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point044.checked)
    (1/1) (by decide +kernel)
#print axioms band223_rank

end ForestUnimodality.IntermediateBridgeRankData
