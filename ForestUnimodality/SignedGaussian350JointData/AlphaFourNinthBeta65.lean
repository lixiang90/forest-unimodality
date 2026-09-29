import ForestUnimodality.SignedGaussian350JointData.AlphaFourNinthBeta65Part00
import ForestUnimodality.SignedGaussian350JointData.AlphaFourNinthBeta65Part01
import ForestUnimodality.SignedGaussian350JointData.AlphaFourNinthBeta65Part02
import ForestUnimodality.SignedGaussian350JointData.AlphaFourNinthBeta65Part03
import ForestUnimodality.SignedGaussian350JointData.AlphaFourNinthBeta65Part04
import ForestUnimodality.SignedGaussian350JointData.AlphaFourNinthBeta65Part05
import ForestUnimodality.SignedGaussian350JointData.AlphaFourNinthBeta65Part06
import ForestUnimodality.SignedGaussian350JointData.AlphaFourNinthBeta65Part07
import ForestUnimodality.SignedGaussian350JointData.AlphaFourNinthBeta65Part08

namespace ForestUnimodality.SignedGaussian350JointData.AlphaFourNinthBeta65
open SignedGaussian350Profile SignedGaussianHermite

noncomputable def beta : ℝ := (13/20)
noncomputable def B : ℝ := (533857/200000)
noncomputable def cuts (i:ℕ) : ℝ := 4/9+(beta-4/9)*(i:ℝ)/40
noncomputable def prices : ℕ→ℝ
  | 0 => (1349448067/5000000000)
  | 1 => (510074213/2000000000)
  | 2 => (1204212613/5000000000)
  | 3 => (2272778411/10000000000)
  | 4 => (1071582141/5000000000)
  | 5 => (1009664767/5000000000)
  | 6 => (1901033111/10000000000)
  | 7 => (3576091/20000000)
  | 8 => (168014803/1000000000)
  | 9 => (1577132269/10000000000)
  | 10 => (184849927/1250000000)
  | 11 => (346239943/2500000000)
  | 12 => (1295432219/10000000000)
  | 13 => (302510937/2500000000)
  | 14 => (564314501/5000000000)
  | 15 => (1051029883/10000000000)
  | 16 => (122136891/1250000000)
  | 17 => (28333749/312500000)
  | 18 => (52477861/625000000)
  | 19 => (193964937/2500000000)
  | 20 => (715194593/10000000000)
  | 21 => (10273879/156250000)
  | 22 => (150685913/2500000000)
  | 23 => (550728407/10000000000)
  | 24 => (501374631/10000000000)
  | 25 => (454578691/10000000000)
  | 26 => (410241007/10000000000)
  | 27 => (92066461/2500000000)
  | 28 => (20535071/625000000)
  | 29 => (72759577/2500000000)
  | 30 => (255612109/10000000000)
  | 31 => (27775057/1250000000)
  | 32 => (2980067/156250000)
  | 33 => (5034607/312500000)
  | 34 => (66638217/5000000000)
  | 35 => (26790127/2500000000)
  | 36 => (1653827/200000000)
  | 37 => (59803049/10000000000)
  | 38 => (3843199/1000000000)
  | 39 => (18516741/10000000000)
  | _ => 0

theorem curvature_lower : -B≤coefficient parameter beta := Node40.curvature_lower

theorem cuts_start : cuts 0=(4/9:ℝ) := by norm_num [cuts]
theorem cuts_end : cuts 40=beta := by norm_num [cuts]
theorem cuts_steps (i:ℕ) : cuts i≤cuts (i+1) := by
  norm_num [cuts,beta,Nat.cast_add]; linarith

theorem prices_upper (i:ℕ) (hi:i≤39) : positiveGap parameter (-B) (cuts i)≤prices i := by
  interval_cases i
  · convert! Node00.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node01.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node02.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node03.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node04.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node05.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node06.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node07.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node08.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node09.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node10.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node11.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node12.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node13.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node14.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node15.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node16.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node17.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node18.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node19.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node20.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node21.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node22.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node23.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node24.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node25.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node26.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node27.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node28.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node29.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node30.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node31.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node32.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node33.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node34.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node35.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node36.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node37.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node38.gap_upper using 1; norm_num [cuts,beta,B,prices]
  · convert! Node39.gap_upper using 1; norm_num [cuts,beta,B,prices]

theorem prices_nonneg (i:ℕ) (hi:i≤39) : 0≤prices i := by
  interval_cases i <;> norm_num [prices]

theorem prices_decreasing (i:ℕ) (hi:i<39) : prices (i+1)≤prices i := by
  interval_cases i <;> norm_num [prices]

theorem prices_end : prices 40=0 := rfl

#print axioms curvature_lower
#print axioms prices_upper
#print axioms prices_decreasing
end ForestUnimodality.SignedGaussian350JointData.AlphaFourNinthBeta65
