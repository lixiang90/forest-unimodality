import ForestUnimodality.SignedGaussian350Data.Beta60Part00
import ForestUnimodality.SignedGaussian350Data.Beta60Part01
import ForestUnimodality.SignedGaussian350Data.Beta60Part02
import ForestUnimodality.SignedGaussian350Data.Beta60Part03
import ForestUnimodality.SignedGaussian350Data.Beta60Part04
import ForestUnimodality.SignedGaussian350Data.Beta60Part05
import ForestUnimodality.SignedGaussian350Data.Beta60Part06
import ForestUnimodality.SignedGaussian350Data.Beta60Part07
import ForestUnimodality.SignedGaussian350Data.Beta60Part08

namespace ForestUnimodality.SignedGaussian350Data.Beta60
open SignedGaussian350Profile SignedGaussianHermite

noncomputable def beta : ℝ := (3/5)
noncomputable def B : ℝ := (1411639/500000)
noncomputable def cuts (i:ℕ) : ℝ := 7/20+(beta-7/20)*(i:ℝ)/40
noncomputable def prices : ℕ→ℝ
  | 0 => (3205803301/5000000000)
  | 1 => (600776867/1000000000)
  | 2 => (5626925069/10000000000)
  | 3 => (1316913863/2500000000)
  | 4 => (616080739/1250000000)
  | 5 => (4608679403/10000000000)
  | 6 => (538328389/1250000000)
  | 7 => (2010720401/5000000000)
  | 8 => (750429167/2000000000)
  | 9 => (3497834973/10000000000)
  | 10 => (1628831367/5000000000)
  | 11 => (3030840329/10000000000)
  | 12 => (2816631053/10000000000)
  | 13 => (653586533/2500000000)
  | 14 => (2423340957/10000000000)
  | 15 => (224301163/1000000000)
  | 16 => (207279187/1000000000)
  | 17 => (1912150153/10000000000)
  | 18 => (1760587127/10000000000)
  | 19 => (404408309/2500000000)
  | 20 => (185355821/1250000000)
  | 21 => (67790543/500000000)
  | 22 => (309033423/2500000000)
  | 23 => (140430601/1250000000)
  | 24 => (254348649/2500000000)
  | 25 => (14338323/156250000)
  | 26 => (411953293/5000000000)
  | 27 => (147172127/2000000000)
  | 28 => (653234747/10000000000)
  | 29 => (575763477/10000000000)
  | 30 => (31449691/625000000)
  | 31 => (87058107/2000000000)
  | 32 => (185911483/5000000000)
  | 33 => (312576669/10000000000)
  | 34 => (257346527/10000000000)
  | 35 => (102968679/5000000000)
  | 36 => (31632661/2000000000)
  | 37 => (56923647/5000000000)
  | 38 => (72820511/10000000000)
  | 39 => (34921923/10000000000)
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
end ForestUnimodality.SignedGaussian350Data.Beta60
