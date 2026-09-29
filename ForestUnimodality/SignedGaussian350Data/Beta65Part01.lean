import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.SignedGaussian350Profile

namespace ForestUnimodality.SignedGaussian350Data.Beta65
open AnalyticNumericCertificate SignedGaussian350Profile SignedGaussianProfile SignedGaussianHermite
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Node05
private def e000 : Expr := .rat (31 / 80)
private def e001 : Expr := .sqrt e000 (3112474899497183 / 5000000000000000) (6224949798994367 / 10000000000000000)
private def e002 : Expr := .exp (-797408379 / 625000000) (279192601770963 / 1000000000000000) (2791926017709631 / 10000000000000000) { parts := 2, inner := (-797408379 / 1250000000), terms := 32, innerLo := (264193395910535141829353 / 500000000000000000000000), innerHi := (528386791821070283658707 / 1000000000000000000000000) }
private def e003 : Expr := .exp (-9 / 20) (1594070379054433 / 2500000000000000) (6376281516217733 / 10000000000000000) { parts := 1, inner := (-9 / 20), terms := 32, innerLo := (637628151621773293143743 / 1000000000000000000000000), innerHi := (9962939869090207705371 / 15625000000000000000000) }
private def e004 : Expr := .rat (21 / 10)
private def e005 : Expr := .mul e004 e003
private def e006 : Expr := .rat (961 / 6400)
private def e007 : Expr := .mul e005 e006
private def e008 : Expr := .mul e007 e001
private def e009 : Expr := .rat (140091621 / 312500000)
private def e010 : Expr := .mul e009 e002
private def e011 : Expr := .sub e008 e010
private def e012 : Expr := .rat (-191357504461907641 / 195312500000000000)
private def e013 : Expr := .mul e012 e002
private def e014 : Expr := .mul e000 e001
private def e015 : Expr := .inv e014
private def e016 : Expr := .mul e013 e015
private def e017 : Expr := .rat (-11339967379 / 10000000000)
private def e018 : Expr := .sub e016 e017
private def e019 : Expr := .rat (209 / 200)
private def e020 : Expr := .mul e003 e019
private def e021 : Expr := .rat (159 / 200)
private def e022 : Expr := .mul e003 e021
private def e023 : Expr := .rat (-49 / 80)
private def e024 : Expr := .mul e022 e023
private def e025 : Expr := .add e020 e024
private def e026 : Expr := .rat (1281790657 / 1280000000)
private def e027 : Expr := .sub e025 e026
private def e028 : Expr := .rat (1221085369 / 2500000000)
private def e029 : Expr := .rat (-6455625903 / 10000000000)
private def e030 : Expr := .sub e029 e027

private theorem slope_checked : e011.positiveCheck=true := by decide +kernel
private theorem value_checked : e018.positiveCheck=true := by decide +kernel
private theorem gap_checked : e030.positiveCheck=true := by decide +kernel

theorem profile_lower : ((-11339967379 / 10000000000):ℝ)≤profile parameter (31 / 80) := by
  apply profile_lower_sqrt (u:=(797408379 / 625000000)) (by norm_num) (by norm_num) (by norm_num)
  · have h:=e011.positiveCheck_sound slope_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval,parameter] at h ⊢
    nlinarith
  · have h:=e018.positiveCheck_sound value_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv] at h ⊢
    ring_nf at h ⊢
    linarith

theorem gap_upper : positiveGap parameter (-((533857 / 200000):ℝ)) (31 / 80)≤(1221085369 / 2500000000) := by
  apply gap_le_of_profile_lower profile_lower (by norm_num)
  have h:=e030.positiveCheck_sound gap_checked
  norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
  linarith

end Node05

namespace Node06
private def e000 : Expr := .rat (79 / 200)
private def e001 : Expr := .sqrt e000 (6284902544988267 / 10000000000000000) (1571225636247067 / 2500000000000000)
private def e002 : Expr := .exp (-3167342569 / 2500000000) (1408465599920069 / 5000000000000000) (2816931199840139 / 10000000000000000) { parts := 2, inner := (-3167342569 / 5000000000), terms := 32, innerLo := (265373849495392958053463 / 500000000000000000000000), innerHi := (530747698990785916106927 / 1000000000000000000000000) }
private def e003 : Expr := .exp (-9 / 20) (1594070379054433 / 2500000000000000) (6376281516217733 / 10000000000000000) { parts := 1, inner := (-9 / 20), terms := 32, innerLo := (637628151621773293143743 / 1000000000000000000000000), innerHi := (9962939869090207705371 / 15625000000000000000000) }
private def e004 : Expr := .rat (21 / 10)
private def e005 : Expr := .mul e004 e003
private def e006 : Expr := .rat (6241 / 40000)
private def e007 : Expr := .mul e005 e006
private def e008 : Expr := .mul e007 e001
private def e009 : Expr := .rat (582657431 / 1250000000)
private def e010 : Expr := .mul e009 e002
private def e011 : Expr := .sub e008 e010
private def e012 : Expr := .rat (-2947880738149519761 / 3125000000000000000)
private def e013 : Expr := .mul e012 e002
private def e014 : Expr := .mul e000 e001
private def e015 : Expr := .inv e014
private def e016 : Expr := .mul e013 e015
private def e017 : Expr := .rat (-10703861581 / 10000000000)
private def e018 : Expr := .sub e016 e017
private def e019 : Expr := .rat (209 / 200)
private def e020 : Expr := .mul e003 e019
private def e021 : Expr := .rat (159 / 200)
private def e022 : Expr := .mul e003 e021
private def e023 : Expr := .rat (-121 / 200)
private def e024 : Expr := .mul e022 e023
private def e025 : Expr := .add e020 e024
private def e026 : Expr := .rat (7816200337 / 8000000000)
private def e027 : Expr := .sub e025 e026
private def e028 : Expr := .rat (4529993343 / 10000000000)
private def e029 : Expr := .rat (-3086934119 / 5000000000)
private def e030 : Expr := .sub e029 e027

private theorem slope_checked : e011.positiveCheck=true := by decide +kernel
private theorem value_checked : e018.positiveCheck=true := by decide +kernel
private theorem gap_checked : e030.positiveCheck=true := by decide +kernel

theorem profile_lower : ((-10703861581 / 10000000000):ℝ)≤profile parameter (79 / 200) := by
  apply profile_lower_sqrt (u:=(3167342569 / 2500000000)) (by norm_num) (by norm_num) (by norm_num)
  · have h:=e011.positiveCheck_sound slope_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval,parameter] at h ⊢
    nlinarith
  · have h:=e018.positiveCheck_sound value_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv] at h ⊢
    ring_nf at h ⊢
    linarith

theorem gap_upper : positiveGap parameter (-((533857 / 200000):ℝ)) (79 / 200)≤(4529993343 / 10000000000) := by
  apply gap_le_of_profile_lower profile_lower (by norm_num)
  have h:=e030.positiveCheck_sound gap_checked
  norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
  linarith

end Node06

namespace Node07
private def e000 : Expr := .rat (161 / 400)
private def e001 : Expr := .sqrt e000 (158607219255619 / 250000000000000) (6344288770224761 / 10000000000000000)
private def e002 : Expr := .exp (-12579108909 / 10000000000) (2842472301255821 / 10000000000000000) (1421236150627911 / 5000000000000000) { parts := 2, inner := (-12579108909 / 20000000000), terms := 32, innerLo := (13328710321275979185307 / 25000000000000000000000), innerHi := (533148412851039167412281 / 1000000000000000000000000) }
private def e003 : Expr := .exp (-9 / 20) (1594070379054433 / 2500000000000000) (6376281516217733 / 10000000000000000) { parts := 1, inner := (-9 / 20), terms := 32, innerLo := (637628151621773293143743 / 1000000000000000000000000), innerHi := (9962939869090207705371 / 15625000000000000000000) }
private def e004 : Expr := .rat (21 / 10)
private def e005 : Expr := .mul e004 e003
private def e006 : Expr := .rat (25921 / 160000)
private def e007 : Expr := .mul e005 e006
private def e008 : Expr := .mul e007 e001
private def e009 : Expr := .rat (2420891091 / 5000000000)
private def e010 : Expr := .mul e009 e002
private def e011 : Expr := .sub e008 e010
private def e012 : Expr := .rat (-45338436399483170281 / 50000000000000000000)
private def e013 : Expr := .mul e012 e002
private def e014 : Expr := .mul e000 e001
private def e015 : Expr := .inv e014
private def e016 : Expr := .mul e013 e015
private def e017 : Expr := .rat (-5046775113 / 5000000000)
private def e018 : Expr := .sub e016 e017
private def e019 : Expr := .rat (209 / 200)
private def e020 : Expr := .mul e003 e019
private def e021 : Expr := .rat (159 / 200)
private def e022 : Expr := .mul e003 e021
private def e023 : Expr := .rat (-239 / 400)
private def e024 : Expr := .mul e022 e023
private def e025 : Expr := .add e020 e024
private def e026 : Expr := .rat (30494445697 / 32000000000)
private def e027 : Expr := .sub e025 e026
private def e028 : Expr := .rat (1049609177 / 2500000000)
private def e029 : Expr := .rat (-2947556759 / 5000000000)
private def e030 : Expr := .sub e029 e027

private theorem slope_checked : e011.positiveCheck=true := by decide +kernel
private theorem value_checked : e018.positiveCheck=true := by decide +kernel
private theorem gap_checked : e030.positiveCheck=true := by decide +kernel

theorem profile_lower : ((-5046775113 / 5000000000):ℝ)≤profile parameter (161 / 400) := by
  apply profile_lower_sqrt (u:=(12579108909 / 10000000000)) (by norm_num) (by norm_num) (by norm_num)
  · have h:=e011.positiveCheck_sound slope_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval,parameter] at h ⊢
    nlinarith
  · have h:=e018.positiveCheck_sound value_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv] at h ⊢
    ring_nf at h ⊢
    linarith

theorem gap_upper : positiveGap parameter (-((533857 / 200000):ℝ)) (161 / 400)≤(1049609177 / 2500000000) := by
  apply gap_le_of_profile_lower profile_lower (by norm_num)
  have h:=e030.positiveCheck_sound gap_checked
  norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
  linarith

end Node07

namespace Node08
private def e000 : Expr := .rat (41 / 100)
private def e001 : Expr := .sqrt e000 (400195264839553 / 625000000000000) (6403124237432849 / 10000000000000000)
private def e002 : Expr := .exp (-6243898901 / 5000000000) (2868546090666001 / 10000000000000000) (1434273045333001 / 5000000000000000) { parts := 2, inner := (-6243898901 / 10000000000), terms := 32, innerLo := (107117619291431257117913 / 200000000000000000000000), innerHi := (267794048228578142794783 / 500000000000000000000000) }
private def e003 : Expr := .exp (-9 / 20) (1594070379054433 / 2500000000000000) (6376281516217733 / 10000000000000000) { parts := 1, inner := (-9 / 20), terms := 32, innerLo := (637628151621773293143743 / 1000000000000000000000000), innerHi := (9962939869090207705371 / 15625000000000000000000) }
private def e004 : Expr := .rat (21 / 10)
private def e005 : Expr := .mul e004 e003
private def e006 : Expr := .rat (1681 / 10000)
private def e007 : Expr := .mul e005 e006
private def e008 : Expr := .mul e007 e001
private def e009 : Expr := .rat (1256101099 / 2500000000)
private def e010 : Expr := .mul e009 e002
private def e011 : Expr := .sub e008 e010
private def e012 : Expr := .rat (-10876526233409007801 / 12500000000000000000)
private def e013 : Expr := .mul e012 e002
private def e014 : Expr := .mul e000 e001
private def e015 : Expr := .inv e014
private def e016 : Expr := .mul e013 e015
private def e017 : Expr := .rat (-1188437259 / 1250000000)
private def e018 : Expr := .sub e016 e017
private def e019 : Expr := .rat (209 / 200)
private def e020 : Expr := .mul e003 e019
private def e021 : Expr := .rat (159 / 200)
private def e022 : Expr := .mul e003 e021
private def e023 : Expr := .rat (-59 / 100)
private def e024 : Expr := .mul e022 e023
private def e025 : Expr := .add e020 e024
private def e026 : Expr := .rat (1858356217 / 2000000000)
private def e027 : Expr := .sub e025 e026
private def e028 : Expr := .rat (486017041 / 1250000000)
private def e029 : Expr := .rat (-351210109 / 625000000)
private def e030 : Expr := .sub e029 e027

private theorem slope_checked : e011.positiveCheck=true := by decide +kernel
private theorem value_checked : e018.positiveCheck=true := by decide +kernel
private theorem gap_checked : e030.positiveCheck=true := by decide +kernel

theorem profile_lower : ((-1188437259 / 1250000000):ℝ)≤profile parameter (41 / 100) := by
  apply profile_lower_sqrt (u:=(6243898901 / 5000000000)) (by norm_num) (by norm_num) (by norm_num)
  · have h:=e011.positiveCheck_sound slope_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval,parameter] at h ⊢
    nlinarith
  · have h:=e018.positiveCheck_sound value_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv] at h ⊢
    ring_nf at h ⊢
    linarith

theorem gap_upper : positiveGap parameter (-((533857 / 200000):ℝ)) (41 / 100)≤(486017041 / 1250000000) := by
  apply gap_le_of_profile_lower profile_lower (by norm_num)
  have h:=e030.positiveCheck_sound gap_checked
  norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
  linarith

end Node08

namespace Node09
private def e000 : Expr := .rat (167 / 400)
private def e001 : Expr := .sqrt e000 (3230711995830021 / 5000000000000000) (6461423991660043 / 10000000000000000)
private def e002 : Expr := .exp (-6197742043 / 5000000000) (2895149308753651 / 10000000000000000) (723787327188413 / 2500000000000000) { parts := 2, inner := (-6197742043 / 10000000000), terms := 32, innerLo := (134516479212438220942841 / 250000000000000000000000), innerHi := (107613183369950576754273 / 200000000000000000000000) }
private def e003 : Expr := .exp (-9 / 20) (1594070379054433 / 2500000000000000) (6376281516217733 / 10000000000000000) { parts := 1, inner := (-9 / 20), terms := 32, innerLo := (637628151621773293143743 / 1000000000000000000000000), innerHi := (9962939869090207705371 / 15625000000000000000000) }
private def e004 : Expr := .rat (21 / 10)
private def e005 : Expr := .mul e004 e003
private def e006 : Expr := .rat (27889 / 160000)
private def e007 : Expr := .mul e005 e006
private def e008 : Expr := .mul e007 e001
private def e009 : Expr := .rat (1302257957 / 2500000000)
private def e010 : Expr := .mul e009 e002
private def e011 : Expr := .sub e008 e010
private def e012 : Expr := .rat (-10417651324069813849 / 12500000000000000000)
private def e013 : Expr := .mul e012 e002
private def e014 : Expr := .mul e000 e001
private def e015 : Expr := .inv e014
private def e016 : Expr := .mul e013 e015
private def e017 : Expr := .rat (-894429369 / 1000000000)
private def e018 : Expr := .sub e016 e017
private def e019 : Expr := .rat (209 / 200)
private def e020 : Expr := .mul e003 e019
private def e021 : Expr := .rat (159 / 200)
private def e022 : Expr := .mul e003 e021
private def e023 : Expr := .rat (-233 / 400)
private def e024 : Expr := .mul e022 e023
private def e025 : Expr := .add e020 e024
private def e026 : Expr := .rat (28982562673 / 32000000000)
private def e027 : Expr := .sub e025 e026
private def e028 : Expr := .rat (1798840387 / 5000000000)
private def e029 : Expr := .rat (-1336653229 / 2500000000)
private def e030 : Expr := .sub e029 e027

private theorem slope_checked : e011.positiveCheck=true := by decide +kernel
private theorem value_checked : e018.positiveCheck=true := by decide +kernel
private theorem gap_checked : e030.positiveCheck=true := by decide +kernel

theorem profile_lower : ((-894429369 / 1000000000):ℝ)≤profile parameter (167 / 400) := by
  apply profile_lower_sqrt (u:=(6197742043 / 5000000000)) (by norm_num) (by norm_num) (by norm_num)
  · have h:=e011.positiveCheck_sound slope_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval,parameter] at h ⊢
    nlinarith
  · have h:=e018.positiveCheck_sound value_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv] at h ⊢
    ring_nf at h ⊢
    linarith

theorem gap_upper : positiveGap parameter (-((533857 / 200000):ℝ)) (167 / 400)≤(1798840387 / 5000000000) := by
  apply gap_le_of_profile_lower profile_lower (by norm_num)
  have h:=e030.positiveCheck_sound gap_checked
  norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
  linarith

end Node09

#print axioms Node05.profile_lower
#print axioms Node09.gap_upper
end ForestUnimodality.SignedGaussian350Data.Beta65
