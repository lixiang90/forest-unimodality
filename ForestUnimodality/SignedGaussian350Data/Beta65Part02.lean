import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.SignedGaussian350Profile

namespace ForestUnimodality.SignedGaussian350Data.Beta65
open AnalyticNumericCertificate SignedGaussian350Profile SignedGaussianProfile SignedGaussianHermite
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Node10
private def e000 : Expr := .rat (17 / 40)
private def e001 : Expr := .sqrt e000 (814900300650331 / 1250000000000000) (6519202405202649 / 10000000000000000)
private def e002 : Expr := .exp (-6151107059 / 5000000000) (1461139339095681 / 5000000000000000) (2922278678191363 / 10000000000000000) { parts := 2, inner := (-6151107059 / 10000000000), terms := 32, innerLo := (54058104648529463583389 / 100000000000000000000000), innerHi := (540581046485294635833891 / 1000000000000000000000000) }
private def e003 : Expr := .exp (-9 / 20) (1594070379054433 / 2500000000000000) (6376281516217733 / 10000000000000000) { parts := 1, inner := (-9 / 20), terms := 32, innerLo := (637628151621773293143743 / 1000000000000000000000000), innerHi := (9962939869090207705371 / 15625000000000000000000) }
private def e004 : Expr := .rat (21 / 10)
private def e005 : Expr := .mul e004 e003
private def e006 : Expr := .rat (289 / 1600)
private def e007 : Expr := .mul e005 e006
private def e008 : Expr := .mul e007 e001
private def e009 : Expr := .rat (1348892941 / 2500000000)
private def e010 : Expr := .mul e009 e002
private def e011 : Expr := .sub e008 e010
private def e012 : Expr := .rat (-9958350403779629481 / 12500000000000000000)
private def e013 : Expr := .mul e012 e002
private def e014 : Expr := .mul e000 e001
private def e015 : Expr := .inv e014
private def e016 : Expr := .mul e013 e015
private def e017 : Expr := .rat (-8402637443 / 10000000000)
private def e018 : Expr := .sub e016 e017
private def e019 : Expr := .rat (209 / 200)
private def e020 : Expr := .mul e003 e019
private def e021 : Expr := .rat (159 / 200)
private def e022 : Expr := .mul e003 e021
private def e023 : Expr := .rat (-23 / 40)
private def e024 : Expr := .mul e022 e023
private def e025 : Expr := .add e020 e024
private def e026 : Expr := .rat (282410353 / 320000000)
private def e027 : Expr := .sub e025 e026
private def e028 : Expr := .rat (332577041 / 1000000000)
private def e029 : Expr := .rat (-5076867033 / 10000000000)
private def e030 : Expr := .sub e029 e027

private theorem slope_checked : e011.positiveCheck=true := by decide +kernel
private theorem value_checked : e018.positiveCheck=true := by decide +kernel
private theorem gap_checked : e030.positiveCheck=true := by decide +kernel

theorem profile_lower : ((-8402637443 / 10000000000):ℝ)≤profile parameter (17 / 40) := by
  apply profile_lower_sqrt (u:=(6151107059 / 5000000000)) (by norm_num) (by norm_num) (by norm_num)
  · have h:=e011.positiveCheck_sound slope_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval,parameter] at h ⊢
    nlinarith
  · have h:=e018.positiveCheck_sound value_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv] at h ⊢
    ring_nf at h ⊢
    linarith

theorem gap_upper : positiveGap parameter (-((533857 / 200000):ℝ)) (17 / 40)≤(332577041 / 1000000000) := by
  apply gap_le_of_profile_lower profile_lower (by norm_num)
  have h:=e030.positiveCheck_sound gap_checked
  norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
  linarith

end Node10

namespace Node11
private def e000 : Expr := .rat (173 / 400)
private def e001 : Expr := .sqrt e000 (822059152372869 / 1250000000000000) (6576473218982953 / 10000000000000000)
private def e002 : Expr := .exp (-1526004177 / 1250000000) (2949930914883789 / 10000000000000000) (294993091488379 / 1000000000000000) { parts := 2, inner := (-1526004177 / 2500000000), terms := 32, innerLo := (271566332361165017223821 / 500000000000000000000000), innerHi := (543132664722330034447643 / 1000000000000000000000000) }
private def e003 : Expr := .exp (-9 / 20) (1594070379054433 / 2500000000000000) (6376281516217733 / 10000000000000000) { parts := 1, inner := (-9 / 20), terms := 32, innerLo := (637628151621773293143743 / 1000000000000000000000000), innerHi := (9962939869090207705371 / 15625000000000000000000) }
private def e004 : Expr := .rat (21 / 10)
private def e005 : Expr := .mul e004 e003
private def e006 : Expr := .rat (29929 / 160000)
private def e007 : Expr := .mul e005 e006
private def e008 : Expr := .mul e007 e001
private def e009 : Expr := .rat (348995823 / 625000000)
private def e010 : Expr := .mul e009 e002
private def e011 : Expr := .sub e008 e010
private def e012 : Expr := .rat (-593686137596447329 / 781250000000000000)
private def e013 : Expr := .mul e012 e002
private def e014 : Expr := .mul e000 e001
private def e015 : Expr := .inv e014
private def e016 : Expr := .mul e013 e015
private def e017 : Expr := .rat (-1970332697 / 2500000000)
private def e018 : Expr := .sub e016 e017
private def e019 : Expr := .rat (209 / 200)
private def e020 : Expr := .mul e003 e019
private def e021 : Expr := .rat (159 / 200)
private def e022 : Expr := .mul e003 e021
private def e023 : Expr := .rat (-227 / 400)
private def e024 : Expr := .mul e022 e023
private def e025 : Expr := .add e020 e024
private def e026 : Expr := .rat (27509117353 / 32000000000)
private def e027 : Expr := .sub e025 e026
private def e028 : Expr := .rat (767801673 / 2500000000)
private def e029 : Expr := .rat (-75158189 / 156250000)
private def e030 : Expr := .sub e029 e027

private theorem slope_checked : e011.positiveCheck=true := by decide +kernel
private theorem value_checked : e018.positiveCheck=true := by decide +kernel
private theorem gap_checked : e030.positiveCheck=true := by decide +kernel

theorem profile_lower : ((-1970332697 / 2500000000):ℝ)≤profile parameter (173 / 400) := by
  apply profile_lower_sqrt (u:=(1526004177 / 1250000000)) (by norm_num) (by norm_num) (by norm_num)
  · have h:=e011.positiveCheck_sound slope_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval,parameter] at h ⊢
    nlinarith
  · have h:=e018.positiveCheck_sound value_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv] at h ⊢
    ring_nf at h ⊢
    linarith

theorem gap_upper : positiveGap parameter (-((533857 / 200000):ℝ)) (173 / 400)≤(767801673 / 2500000000) := by
  apply gap_le_of_profile_lower profile_lower (by norm_num)
  have h:=e030.positiveCheck_sound gap_checked
  norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
  linarith

end Node11

namespace Node12
private def e000 : Expr := .rat (11 / 25)
private def e001 : Expr := .sqrt e000 (6633249580710799 / 10000000000000000) (16583123951777 / 25000000000000)
private def e002 : Expr := .exp (-12112986613 / 10000000000) (595620547025043 / 2000000000000000) (93065710472663 / 312500000000000) { parts := 2, inner := (-12112986613 / 20000000000), terms := 32, innerLo := (545719958873158231928651 / 1000000000000000000000000), innerHi := (136429989718289557982163 / 250000000000000000000000) }
private def e003 : Expr := .exp (-9 / 20) (1594070379054433 / 2500000000000000) (6376281516217733 / 10000000000000000) { parts := 1, inner := (-9 / 20), terms := 32, innerLo := (637628151621773293143743 / 1000000000000000000000000), innerHi := (9962939869090207705371 / 15625000000000000000000) }
private def e004 : Expr := .rat (21 / 10)
private def e005 : Expr := .mul e004 e003
private def e006 : Expr := .rat (121 / 625)
private def e007 : Expr := .mul e005 e006
private def e008 : Expr := .mul e007 e001
private def e009 : Expr := .rat (2887013387 / 5000000000)
private def e010 : Expr := .mul e009 e002
private def e011 : Expr := .sub e008 e010
private def e012 : Expr := .rat (-36159511621717211769 / 50000000000000000000)
private def e013 : Expr := .mul e012 e002
private def e014 : Expr := .mul e000 e001
private def e015 : Expr := .inv e014
private def e016 : Expr := .mul e013 e015
private def e017 : Expr := .rat (-7379266799 / 10000000000)
private def e018 : Expr := .sub e016 e017
private def e019 : Expr := .rat (209 / 200)
private def e020 : Expr := .mul e003 e019
private def e021 : Expr := .rat (159 / 200)
private def e022 : Expr := .mul e003 e021
private def e023 : Expr := .rat (-14 / 25)
private def e024 : Expr := .mul e022 e023
private def e025 : Expr := .add e020 e024
private def e026 : Expr := .rat (26158993 / 31250000)
private def e027 : Expr := .sub e025 e026
private def e028 : Expr := .rat (1416441347 / 5000000000)
private def e029 : Expr := .rat (-909276821 / 2000000000)
private def e030 : Expr := .sub e029 e027

private theorem slope_checked : e011.positiveCheck=true := by decide +kernel
private theorem value_checked : e018.positiveCheck=true := by decide +kernel
private theorem gap_checked : e030.positiveCheck=true := by decide +kernel

theorem profile_lower : ((-7379266799 / 10000000000):ℝ)≤profile parameter (11 / 25) := by
  apply profile_lower_sqrt (u:=(12112986613 / 10000000000)) (by norm_num) (by norm_num) (by norm_num)
  · have h:=e011.positiveCheck_sound slope_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval,parameter] at h ⊢
    nlinarith
  · have h:=e018.positiveCheck_sound value_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv] at h ⊢
    ring_nf at h ⊢
    linarith

theorem gap_upper : positiveGap parameter (-((533857 / 200000):ℝ)) (11 / 25)≤(1416441347 / 5000000000) := by
  apply gap_le_of_profile_lower profile_lower (by norm_num)
  have h:=e030.positiveCheck_sound gap_checked
  norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
  linarith

end Node12

namespace Node13
private def e000 : Expr := .rat (179 / 400)
private def e001 : Expr := .sqrt e000 (3344772040064913 / 5000000000000000) (6689544080129827 / 10000000000000000)
private def e002 : Expr := .exp (-3004279353 / 2500000000) (1503395431885251 / 5000000000000000) (3006790863770503 / 10000000000000000) { parts := 2, inner := (-3004279353 / 5000000000), terms := 32, innerLo := (8567845707791547080923 / 15625000000000000000000), innerHi := (548342125298659013179073 / 1000000000000000000000000) }
private def e003 : Expr := .exp (-9 / 20) (1594070379054433 / 2500000000000000) (6376281516217733 / 10000000000000000) { parts := 1, inner := (-9 / 20), terms := 32, innerLo := (637628151621773293143743 / 1000000000000000000000000), innerHi := (9962939869090207705371 / 15625000000000000000000) }
private def e004 : Expr := .rat (21 / 10)
private def e005 : Expr := .mul e004 e003
private def e006 : Expr := .rat (32041 / 160000)
private def e007 : Expr := .mul e005 e006
private def e008 : Expr := .mul e007 e001
private def e009 : Expr := .rat (745720647 / 1250000000)
private def e010 : Expr := .mul e009 e002
private def e011 : Expr := .sub e008 e010
private def e012 : Expr := .rat (-2145345239612098609 / 3125000000000000000)
private def e013 : Expr := .mul e012 e002
private def e014 : Expr := .mul e000 e001
private def e015 : Expr := .inv e014
private def e016 : Expr := .mul e013 e015
private def e017 : Expr := .rat (-689542171 / 1000000000)
private def e018 : Expr := .sub e016 e017
private def e019 : Expr := .rat (209 / 200)
private def e020 : Expr := .mul e003 e019
private def e021 : Expr := .rat (159 / 200)
private def e022 : Expr := .mul e003 e021
private def e023 : Expr := .rat (-221 / 400)
private def e024 : Expr := .mul e022 e023
private def e025 : Expr := .add e020 e024
private def e026 : Expr := .rat (26074109737 / 32000000000)
private def e027 : Expr := .sub e025 e026
private def e028 : Expr := .rat (2609774651 / 10000000000)
private def e029 : Expr := .rat (-4285647059 / 10000000000)
private def e030 : Expr := .sub e029 e027

private theorem slope_checked : e011.positiveCheck=true := by decide +kernel
private theorem value_checked : e018.positiveCheck=true := by decide +kernel
private theorem gap_checked : e030.positiveCheck=true := by decide +kernel

theorem profile_lower : ((-689542171 / 1000000000):ℝ)≤profile parameter (179 / 400) := by
  apply profile_lower_sqrt (u:=(3004279353 / 2500000000)) (by norm_num) (by norm_num) (by norm_num)
  · have h:=e011.positiveCheck_sound slope_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval,parameter] at h ⊢
    nlinarith
  · have h:=e018.positiveCheck_sound value_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv] at h ⊢
    ring_nf at h ⊢
    linarith

theorem gap_upper : positiveGap parameter (-((533857 / 200000):ℝ)) (179 / 400)≤(2609774651 / 10000000000) := by
  apply gap_le_of_profile_lower profile_lower (by norm_num)
  have h:=e030.positiveCheck_sound gap_checked
  norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
  linarith

end Node13

namespace Node14
private def e000 : Expr := .rat (91 / 200)
private def e001 : Expr := .sqrt e000 (337268439080801 / 500000000000000) (6745368781616021 / 10000000000000000)
private def e002 : Expr := .exp (-186257321 / 156250000) (1517996021419299 / 5000000000000000) (3035992042838599 / 10000000000000000) { parts := 2, inner := (-186257321 / 312500000), terms := 32, innerLo := (275499185245555582705567 / 500000000000000000000000), innerHi := (110199674098222233082227 / 200000000000000000000000) }
private def e003 : Expr := .exp (-9 / 20) (1594070379054433 / 2500000000000000) (6376281516217733 / 10000000000000000) { parts := 1, inner := (-9 / 20), terms := 32, innerLo := (637628151621773293143743 / 1000000000000000000000000), innerHi := (9962939869090207705371 / 15625000000000000000000) }
private def e004 : Expr := .rat (21 / 10)
private def e005 : Expr := .mul e004 e003
private def e006 : Expr := .rat (8281 / 40000)
private def e007 : Expr := .mul e005 e006
private def e008 : Expr := .mul e007 e001
private def e009 : Expr := .rat (48117679 / 78125000)
private def e010 : Expr := .mul e009 e002
private def e011 : Expr := .sub e008 e010
private def e012 : Expr := .rat (-7933405172972041 / 12207031250000000)
private def e013 : Expr := .mul e012 e002
private def e014 : Expr := .mul e000 e001
private def e015 : Expr := .inv e014
private def e016 : Expr := .mul e013 e015
private def e017 : Expr := .rat (-1285769467 / 2000000000)
private def e018 : Expr := .sub e016 e017
private def e019 : Expr := .rat (209 / 200)
private def e020 : Expr := .mul e003 e019
private def e021 : Expr := .rat (159 / 200)
private def e022 : Expr := .mul e003 e021
private def e023 : Expr := .rat (-109 / 200)
private def e024 : Expr := .mul e022 e023
private def e025 : Expr := .add e020 e024
private def e026 : Expr := .rat (6342755017 / 8000000000)
private def e027 : Expr := .sub e025 e026
private def e028 : Expr := .rat (300116797 / 1250000000)
private def e029 : Expr := .rat (-4027912959 / 10000000000)
private def e030 : Expr := .sub e029 e027

private theorem slope_checked : e011.positiveCheck=true := by decide +kernel
private theorem value_checked : e018.positiveCheck=true := by decide +kernel
private theorem gap_checked : e030.positiveCheck=true := by decide +kernel

theorem profile_lower : ((-1285769467 / 2000000000):ℝ)≤profile parameter (91 / 200) := by
  apply profile_lower_sqrt (u:=(186257321 / 156250000)) (by norm_num) (by norm_num) (by norm_num)
  · have h:=e011.positiveCheck_sound slope_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval,parameter] at h ⊢
    nlinarith
  · have h:=e018.positiveCheck_sound value_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv] at h ⊢
    ring_nf at h ⊢
    linarith

theorem gap_upper : positiveGap parameter (-((533857 / 200000):ℝ)) (91 / 200)≤(300116797 / 1250000000) := by
  apply gap_le_of_profile_lower profile_lower (by norm_num)
  have h:=e030.positiveCheck_sound gap_checked
  norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
  linarith

end Node14

#print axioms Node10.profile_lower
#print axioms Node14.gap_upper
end ForestUnimodality.SignedGaussian350Data.Beta65
