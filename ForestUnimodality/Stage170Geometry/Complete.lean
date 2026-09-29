import ForestUnimodality.Stage170Geometry.Batch000_009
import ForestUnimodality.Stage170Geometry.Batch010_019
import ForestUnimodality.Stage170Geometry.Batch020_029
import ForestUnimodality.Stage170Geometry.Batch030_039
import ForestUnimodality.Stage170Geometry.Batch040_049
import ForestUnimodality.Stage170Geometry.Batch050_059
import ForestUnimodality.Stage170Geometry.Batch060_069
import ForestUnimodality.Stage170Geometry.Batch070_079
import ForestUnimodality.Stage170Geometry.Batch080_089
import ForestUnimodality.Stage170Geometry.Batch090_099
import ForestUnimodality.Stage170Geometry.Batch100_109
import ForestUnimodality.Stage170Geometry.Batch110_119
import ForestUnimodality.Stage170Geometry.Batch120_129

namespace ForestUnimodality.Stage170Geometry
open FiniteRectangleCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem strips_checked (i : Fin 130) : (strip i).check rectangle = true := by
  fin_cases i
  · exact strip000_checked
  · exact strip001_checked
  · exact strip002_checked
  · exact strip003_checked
  · exact strip004_checked
  · exact strip005_checked
  · exact strip006_checked
  · exact strip007_checked
  · exact strip008_checked
  · exact strip009_checked
  · exact strip010_checked
  · exact strip011_checked
  · exact strip012_checked
  · exact strip013_checked
  · exact strip014_checked
  · exact strip015_checked
  · exact strip016_checked
  · exact strip017_checked
  · exact strip018_checked
  · exact strip019_checked
  · exact strip020_checked
  · exact strip021_checked
  · exact strip022_checked
  · exact strip023_checked
  · exact strip024_checked
  · exact strip025_checked
  · exact strip026_checked
  · exact strip027_checked
  · exact strip028_checked
  · exact strip029_checked
  · exact strip030_checked
  · exact strip031_checked
  · exact strip032_checked
  · exact strip033_checked
  · exact strip034_checked
  · exact strip035_checked
  · exact strip036_checked
  · exact strip037_checked
  · exact strip038_checked
  · exact strip039_checked
  · exact strip040_checked
  · exact strip041_checked
  · exact strip042_checked
  · exact strip043_checked
  · exact strip044_checked
  · exact strip045_checked
  · exact strip046_checked
  · exact strip047_checked
  · exact strip048_checked
  · exact strip049_checked
  · exact strip050_checked
  · exact strip051_checked
  · exact strip052_checked
  · exact strip053_checked
  · exact strip054_checked
  · exact strip055_checked
  · exact strip056_checked
  · exact strip057_checked
  · exact strip058_checked
  · exact strip059_checked
  · exact strip060_checked
  · exact strip061_checked
  · exact strip062_checked
  · exact strip063_checked
  · exact strip064_checked
  · exact strip065_checked
  · exact strip066_checked
  · exact strip067_checked
  · exact strip068_checked
  · exact strip069_checked
  · exact strip070_checked
  · exact strip071_checked
  · exact strip072_checked
  · exact strip073_checked
  · exact strip074_checked
  · exact strip075_checked
  · exact strip076_checked
  · exact strip077_checked
  · exact strip078_checked
  · exact strip079_checked
  · exact strip080_checked
  · exact strip081_checked
  · exact strip082_checked
  · exact strip083_checked
  · exact strip084_checked
  · exact strip085_checked
  · exact strip086_checked
  · exact strip087_checked
  · exact strip088_checked
  · exact strip089_checked
  · exact strip090_checked
  · exact strip091_checked
  · exact strip092_checked
  · exact strip093_checked
  · exact strip094_checked
  · exact strip095_checked
  · exact strip096_checked
  · exact strip097_checked
  · exact strip098_checked
  · exact strip099_checked
  · exact strip100_checked
  · exact strip101_checked
  · exact strip102_checked
  · exact strip103_checked
  · exact strip104_checked
  · exact strip105_checked
  · exact strip106_checked
  · exact strip107_checked
  · exact strip108_checked
  · exact strip109_checked
  · exact strip110_checked
  · exact strip111_checked
  · exact strip112_checked
  · exact strip113_checked
  · exact strip114_checked
  · exact strip115_checked
  · exact strip116_checked
  · exact strip117_checked
  · exact strip118_checked
  · exact strip119_checked
  · exact strip120_checked
  · exact strip121_checked
  · exact strip122_checked
  · exact strip123_checked
  · exact strip124_checked
  · exact strip125_checked
  · exact strip126_checked
  · exact strip127_checked
  · exact strip128_checked
  · exact strip129_checked

theorem sources_checked (i : Fin 130) : (strip i).sourceCheck (window i) 170 = true := by
  fin_cases i
  · exact source000_checked
  · exact source001_checked
  · exact source002_checked
  · exact source003_checked
  · exact source004_checked
  · exact source005_checked
  · exact source006_checked
  · exact source007_checked
  · exact source008_checked
  · exact source009_checked
  · exact source010_checked
  · exact source011_checked
  · exact source012_checked
  · exact source013_checked
  · exact source014_checked
  · exact source015_checked
  · exact source016_checked
  · exact source017_checked
  · exact source018_checked
  · exact source019_checked
  · exact source020_checked
  · exact source021_checked
  · exact source022_checked
  · exact source023_checked
  · exact source024_checked
  · exact source025_checked
  · exact source026_checked
  · exact source027_checked
  · exact source028_checked
  · exact source029_checked
  · exact source030_checked
  · exact source031_checked
  · exact source032_checked
  · exact source033_checked
  · exact source034_checked
  · exact source035_checked
  · exact source036_checked
  · exact source037_checked
  · exact source038_checked
  · exact source039_checked
  · exact source040_checked
  · exact source041_checked
  · exact source042_checked
  · exact source043_checked
  · exact source044_checked
  · exact source045_checked
  · exact source046_checked
  · exact source047_checked
  · exact source048_checked
  · exact source049_checked
  · exact source050_checked
  · exact source051_checked
  · exact source052_checked
  · exact source053_checked
  · exact source054_checked
  · exact source055_checked
  · exact source056_checked
  · exact source057_checked
  · exact source058_checked
  · exact source059_checked
  · exact source060_checked
  · exact source061_checked
  · exact source062_checked
  · exact source063_checked
  · exact source064_checked
  · exact source065_checked
  · exact source066_checked
  · exact source067_checked
  · exact source068_checked
  · exact source069_checked
  · exact source070_checked
  · exact source071_checked
  · exact source072_checked
  · exact source073_checked
  · exact source074_checked
  · exact source075_checked
  · exact source076_checked
  · exact source077_checked
  · exact source078_checked
  · exact source079_checked
  · exact source080_checked
  · exact source081_checked
  · exact source082_checked
  · exact source083_checked
  · exact source084_checked
  · exact source085_checked
  · exact source086_checked
  · exact source087_checked
  · exact source088_checked
  · exact source089_checked
  · exact source090_checked
  · exact source091_checked
  · exact source092_checked
  · exact source093_checked
  · exact source094_checked
  · exact source095_checked
  · exact source096_checked
  · exact source097_checked
  · exact source098_checked
  · exact source099_checked
  · exact source100_checked
  · exact source101_checked
  · exact source102_checked
  · exact source103_checked
  · exact source104_checked
  · exact source105_checked
  · exact source106_checked
  · exact source107_checked
  · exact source108_checked
  · exact source109_checked
  · exact source110_checked
  · exact source111_checked
  · exact source112_checked
  · exact source113_checked
  · exact source114_checked
  · exact source115_checked
  · exact source116_checked
  · exact source117_checked
  · exact source118_checked
  · exact source119_checked
  · exact source120_checked
  · exact source121_checked
  · exact source122_checked
  · exact source123_checked
  · exact source124_checked
  · exact source125_checked
  · exact source126_checked
  · exact source127_checked
  · exact source128_checked
  · exact source129_checked

theorem horizontal_checked : chainCheck (fun i => ((strip i).qlo, (strip i).qhi))
    (List.finRange 130) (1/4) (9/13) = true := by decide +kernel

variable {V : Type*} [DecidableEq V]

theorem actual_coverage {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hn : 170 ≤ S.card)
    (hq : z / (1 + z) ∈ Set.Icc (1/4 : ℝ) (9/13 : ℝ))
    (hrank : (S.card : ℝ) / 4 ≤ hardCoreMean G S z) :
    (∃ i : Fin 558, (rectangle i).Contains (z / (1 + z)) (hardCoreAvailableMean G S B z)) ∨
    (∃ p : Fin 43, z ∈ Set.Icc ((Stage350SourceTable.row p).a : ℝ)
      ((Stage350SourceTable.row p).b : ℝ) ∧
      ((Stage350SourceTable.row p).start : ℝ) ≤ hardCoreAvailableMean G S B z) := by
  exact actual_rectangle_or_parent rectangle strip window (List.finRange 130) (1/4) (9/13) 170
    horizontal_checked (fun i _ => strips_checked i) (fun i _ => window_valid i)
    (fun i _ => sources_checked i) hB hG hz hn (by norm_num; exact hq) hrank

#print axioms strips_checked
#print axioms sources_checked
#print axioms horizontal_checked
#print axioms actual_coverage
end ForestUnimodality.Stage170Geometry
