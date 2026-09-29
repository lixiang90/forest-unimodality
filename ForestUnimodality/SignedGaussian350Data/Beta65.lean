import ForestUnimodality.SignedGaussian350Data.Beta65Part00
import ForestUnimodality.SignedGaussian350Data.Beta65Part01
import ForestUnimodality.SignedGaussian350Data.Beta65Part02
import ForestUnimodality.SignedGaussian350Data.Beta65Part03
import ForestUnimodality.SignedGaussian350Data.Beta65Part04
import ForestUnimodality.SignedGaussian350Data.Beta65Part05
import ForestUnimodality.SignedGaussian350Data.Beta65Part06
import ForestUnimodality.SignedGaussian350Data.Beta65Part07
import ForestUnimodality.SignedGaussian350Data.Beta65Part08

namespace ForestUnimodality.SignedGaussian350Data.Beta65
open SignedGaussian350Profile SignedGaussianHermite

noncomputable def beta : ℝ := (13/20)
noncomputable def B : ℝ := (533857/200000)
noncomputable def cuts (i:ℕ) : ℝ := 7/20+(beta-7/20)*(i:ℝ)/40
noncomputable def prices : ℕ→ℝ
  | 0 => (7062227027/10000000000)
  | 1 => (3282750099/5000000000)
  | 2 => (6101642473/10000000000)
  | 3 => (5668255539/10000000000)
  | 4 => (2631576871/5000000000)
  | 5 => (1221085369/2500000000)
  | 6 => (4529993343/10000000000)
  | 7 => (1049609177/2500000000)
  | 8 => (486017041/1250000000)
  | 9 => (1798840387/5000000000)
  | 10 => (332577041/1000000000)
  | 11 => (767801673/2500000000)
  | 12 => (1416441347/5000000000)
  | 13 => (2609774651/10000000000)
  | 14 => (300116797/1250000000)
  | 15 => (68921329/312500000)
  | 16 => (101130127/500000000)
  | 17 => (74061407/400000000)
  | 18 => (1691573643/10000000000)
  | 19 => (771029593/5000000000)
  | 20 => (175297137/1250000000)
  | 21 => (158994141/1250000000)
  | 22 => (1150250247/10000000000)
  | 23 => (1036765663/10000000000)
  | 24 => (232757043/2500000000)
  | 25 => (208148927/2500000000)
  | 26 => (741053133/10000000000)
  | 27 => (656010219/10000000000)
  | 28 => (577099801/10000000000)
  | 29 => (251988047/5000000000)
  | 30 => (436313161/10000000000)
  | 31 => (186901743/5000000000)
  | 32 => (316156693/10000000000)
  | 33 => (263098357/10000000000)
  | 34 => (107184453/5000000000)
  | 35 => (42430657/2500000000)
  | 36 => (64463369/5000000000)
  | 37 => (45880263/5000000000)
  | 38 => (3625911/625000000)
  | 39 => (27490041/10000000000)
  | _ => 0

theorem curvature_lower : -B≤coefficient parameter beta := Node40.curvature_lower

theorem cuts_start : cuts 0=(7/20:ℝ) := by norm_num [cuts]
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
end ForestUnimodality.SignedGaussian350Data.Beta65
