import ForestUnimodality.IntermediateBridgeRank
import ForestUnimodality.IntermediateBridgeCoverData.Batch480_495
import ForestUnimodality.ActivityPointDensityData.Point105

namespace ForestUnimodality.IntermediateBridgeRankData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem band480_rank : band480.RankValid := by
  exact band480.rank_of_certificate ActivityPointDensityData.Point105.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point105.checked)
    (10069993247982499874867565440498371144113/10000000000000000000000000000000000000000) (by decide +kernel)
#print axioms band480_rank

theorem band481_rank : band481.RankValid := by
  exact band481.rank_of_certificate ActivityPointDensityData.Point105.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point105.checked)
    (10069993247982499874867565440498371144113/10000000000000000000000000000000000000000) (by decide +kernel)
#print axioms band481_rank

theorem band482_rank : band482.RankValid := by
  exact band482.rank_of_certificate ActivityPointDensityData.Point105.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point105.checked)
    (10069993247982499874867565440498371144113/10000000000000000000000000000000000000000) (by decide +kernel)
#print axioms band482_rank

theorem band483_rank : band483.RankValid := by
  exact band483.rank_of_certificate ActivityPointDensityData.Point105.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point105.checked)
    (10069993247982499874867565440498371144113/10000000000000000000000000000000000000000) (by decide +kernel)
#print axioms band483_rank

theorem band484_rank : band484.RankValid := by
  exact band484.rank_of_certificate ActivityPointDensityData.Point105.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point105.checked)
    (10079795638357557538433619616096493101723/10000000000000000000000000000000000000000) (by decide +kernel)
#print axioms band484_rank

theorem band485_rank : band485.RankValid := by
  exact band485.rank_of_certificate ActivityPointDensityData.Point105.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point105.checked)
    (10079795638357557538433619616096493101723/10000000000000000000000000000000000000000) (by decide +kernel)
#print axioms band485_rank

theorem band486_rank : band486.RankValid := by
  exact band486.rank_of_certificate ActivityPointDensityData.Point105.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point105.checked)
    (10079795638357557538433619616096493101723/10000000000000000000000000000000000000000) (by decide +kernel)
#print axioms band486_rank

theorem band487_rank : band487.RankValid := by
  exact band487.rank_of_certificate ActivityPointDensityData.Point105.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point105.checked)
    (10079795638357557538433619616096493101723/10000000000000000000000000000000000000000) (by decide +kernel)
#print axioms band487_rank

theorem band488_rank : band488.RankValid := by
  exact band488.rank_of_certificate ActivityPointDensityData.Point105.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point105.checked)
    (403583540214793089934668299961667176393/400000000000000000000000000000000000000) (by decide +kernel)
#print axioms band488_rank

theorem band489_rank : band489.RankValid := by
  exact band489.rank_of_certificate ActivityPointDensityData.Point105.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point105.checked)
    (403583540214793089934668299961667176393/400000000000000000000000000000000000000) (by decide +kernel)
#print axioms band489_rank

theorem band490_rank : band490.RankValid := by
  exact band490.rank_of_certificate ActivityPointDensityData.Point105.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point105.checked)
    (403583540214793089934668299961667176393/400000000000000000000000000000000000000) (by decide +kernel)
#print axioms band490_rank

theorem band491_rank : band491.RankValid := by
  exact band491.rank_of_certificate ActivityPointDensityData.Point105.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point105.checked)
    (403583540214793089934668299961667176393/400000000000000000000000000000000000000) (by decide +kernel)
#print axioms band491_rank

theorem band492_rank : band492.RankValid := by
  exact band492.rank_of_certificate ActivityPointDensityData.Point105.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point105.checked)
    (631210742295145409140639326803466444499/625000000000000000000000000000000000000) (by decide +kernel)
#print axioms band492_rank

theorem band493_rank : band493.RankValid := by
  exact band493.rank_of_certificate ActivityPointDensityData.Point105.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point105.checked)
    (631210742295145409140639326803466444499/625000000000000000000000000000000000000) (by decide +kernel)
#print axioms band493_rank

theorem band494_rank : band494.RankValid := by
  exact band494.rank_of_certificate ActivityPointDensityData.Point105.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point105.checked)
    (631210742295145409140639326803466444499/625000000000000000000000000000000000000) (by decide +kernel)
#print axioms band494_rank

theorem band495_rank : band495.RankValid := by
  exact band495.rank_of_certificate ActivityPointDensityData.Point105.certificate
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point105.checked)
    (631210742295145409140639326803466444499/625000000000000000000000000000000000000) (by decide +kernel)
#print axioms band495_rank

end ForestUnimodality.IntermediateBridgeRankData
