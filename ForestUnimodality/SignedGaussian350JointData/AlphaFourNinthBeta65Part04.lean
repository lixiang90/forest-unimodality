import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.SignedGaussian350Profile

namespace ForestUnimodality.SignedGaussian350JointData.AlphaFourNinthBeta65
open AnalyticNumericCertificate SignedGaussian350Profile SignedGaussianProfile SignedGaussianHermite
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Node20
private def e000 : Expr := .rat (197 / 360)
private def e001 : Expr := .sqrt e000 (3698723503528691 / 5000000000000000) (7397447007057383 / 10000000000000000)
private def e002 : Expr := .exp (-66771317 / 62500000) (1717890080502693 / 5000000000000000) (3435780161005387 / 10000000000000000) { parts := 2, inner := (-66771317 / 125000000), terms := 32, innerLo := (293077641632954769808307 / 500000000000000000000000), innerHi := (117231056653181907923323 / 200000000000000000000000) }
private def e003 : Expr := .exp (-9 / 20) (1594070379054433 / 2500000000000000) (6376281516217733 / 10000000000000000) { parts := 1, inner := (-9 / 20), terms := 32, innerLo := (637628151621773293143743 / 1000000000000000000000000), innerHi := (9962939869090207705371 / 15625000000000000000000) }
private def e004 : Expr := .rat (21 / 10)
private def e005 : Expr := .mul e004 e003
private def e006 : Expr := .rat (38809 / 129600)
private def e007 : Expr := .mul e005 e006
private def e008 : Expr := .mul e007 e001
private def e009 : Expr := .rat (26978683 / 31250000)
private def e010 : Expr := .mul e009 e002
private def e011 : Expr := .sub e008 e010
private def e012 : Expr := .rat (-418680117664489 / 1953125000000000)
private def e013 : Expr := .mul e012 e002
private def e014 : Expr := .mul e000 e001
private def e015 : Expr := .inv e014
private def e016 : Expr := .mul e013 e015
private def e017 : Expr := .rat (-56856759 / 312500000)
private def e018 : Expr := .sub e016 e017
private def e019 : Expr := .rat (209 / 200)
private def e020 : Expr := .mul e003 e019
private def e021 : Expr := .rat (159 / 200)
private def e022 : Expr := .mul e003 e021
private def e023 : Expr := .rat (-163 / 360)
private def e024 : Expr := .mul e022 e023
private def e025 : Expr := .add e020 e024
private def e026 : Expr := .rat (14184046633 / 25920000000)
private def e027 : Expr := .sub e025 e026
private def e028 : Expr := .rat (715194593 / 10000000000)
private def e029 : Expr := .rat (-220844339 / 2000000000)
private def e030 : Expr := .sub e029 e027

private theorem slope_checked : e011.positiveCheck=true := by decide +kernel
private theorem value_checked : e018.positiveCheck=true := by decide +kernel
private theorem gap_checked : e030.positiveCheck=true := by decide +kernel

theorem profile_lower : ((-56856759 / 312500000):ℝ)≤profile parameter (197 / 360) := by
  apply profile_lower_sqrt (u:=(66771317 / 62500000)) (by norm_num) (by norm_num) (by norm_num)
  · have h:=e011.positiveCheck_sound slope_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval,parameter] at h ⊢
    nlinarith
  · have h:=e018.positiveCheck_sound value_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv] at h ⊢
    ring_nf at h ⊢
    linarith

theorem gap_upper : positiveGap parameter (-((533857 / 200000):ℝ)) (197 / 360)≤(715194593 / 10000000000) := by
  apply gap_le_of_profile_lower profile_lower (by norm_num)
  have h:=e030.positiveCheck_sound gap_checked
  norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
  linarith

end Node20

namespace Node21
private def e000 : Expr := .rat (3977 / 7200)
private def e001 : Expr := .sqrt e000 (3716050023583883 / 5000000000000000) (7432100047167767 / 10000000000000000)
private def e002 : Expr := .exp (-1061255331 / 1000000000) (3460211664792479 / 10000000000000000) (21626322904953 / 62500000000000) { parts := 2, inner := (-1061255331 / 2000000000), terms := 32, innerLo := (588235638566083433995709 / 1000000000000000000000000), innerHi := (58823563856608343399571 / 100000000000000000000000) }
private def e003 : Expr := .exp (-9 / 20) (1594070379054433 / 2500000000000000) (6376281516217733 / 10000000000000000) { parts := 1, inner := (-9 / 20), terms := 32, innerLo := (637628151621773293143743 / 1000000000000000000000000), innerHi := (9962939869090207705371 / 15625000000000000000000) }
private def e004 : Expr := .rat (21 / 10)
private def e005 : Expr := .mul e004 e003
private def e006 : Expr := .rat (15816529 / 51840000)
private def e007 : Expr := .mul e005 e006
private def e008 : Expr := .mul e007 e001
private def e009 : Expr := .rat (438744669 / 500000000)
private def e010 : Expr := .mul e009 e002
private def e011 : Expr := .sub e008 e010
private def e012 : Expr := .rat (-95635212075919561 / 500000000000000000)
private def e013 : Expr := .mul e012 e002
private def e014 : Expr := .mul e000 e001
private def e015 : Expr := .inv e014
private def e016 : Expr := .mul e013 e015
private def e017 : Expr := .rat (-806094299 / 5000000000)
private def e018 : Expr := .sub e016 e017
private def e019 : Expr := .rat (209 / 200)
private def e020 : Expr := .mul e003 e019
private def e021 : Expr := .rat (159 / 200)
private def e022 : Expr := .mul e003 e021
private def e023 : Expr := .rat (-3223 / 7200)
private def e024 : Expr := .mul e022 e023
private def e025 : Expr := .add e020 e024
private def e026 : Expr := .rat (5545561840753 / 10368000000000)
private def e027 : Expr := .sub e025 e026
private def e028 : Expr := .rat (10273879 / 156250000)
private def e029 : Expr := .rat (-477330171 / 5000000000)
private def e030 : Expr := .sub e029 e027

private theorem slope_checked : e011.positiveCheck=true := by decide +kernel
private theorem value_checked : e018.positiveCheck=true := by decide +kernel
private theorem gap_checked : e030.positiveCheck=true := by decide +kernel

theorem profile_lower : ((-806094299 / 5000000000):ℝ)≤profile parameter (3977 / 7200) := by
  apply profile_lower_sqrt (u:=(1061255331 / 1000000000)) (by norm_num) (by norm_num) (by norm_num)
  · have h:=e011.positiveCheck_sound slope_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval,parameter] at h ⊢
    nlinarith
  · have h:=e018.positiveCheck_sound value_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv] at h ⊢
    ring_nf at h ⊢
    linarith

theorem gap_upper : positiveGap parameter (-((533857 / 200000):ℝ)) (3977 / 7200)≤(10273879 / 156250000) := by
  apply gap_le_of_profile_lower profile_lower (by norm_num)
  have h:=e030.positiveCheck_sound gap_checked
  norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
  linarith

end Node21

namespace Node22
private def e000 : Expr := .rat (223 / 400)
private def e001 : Expr := .sqrt e000 (7466592261534039 / 10000000000000000) (186664806538351 / 250000000000000)
private def e002 : Expr := .exp (-5270779401 / 5000000000) (108902021097943 / 312500000000000) (3484864675134177 / 10000000000000000) { parts := 2, inner := (-5270779401 / 10000000000), terms := 32, innerLo := (590327423988939933036919 / 1000000000000000000000000), innerHi := (14758185599723498325923 / 25000000000000000000000) }
private def e003 : Expr := .exp (-9 / 20) (1594070379054433 / 2500000000000000) (6376281516217733 / 10000000000000000) { parts := 1, inner := (-9 / 20), terms := 32, innerLo := (637628151621773293143743 / 1000000000000000000000000), innerHi := (9962939869090207705371 / 15625000000000000000000) }
private def e004 : Expr := .rat (21 / 10)
private def e005 : Expr := .mul e004 e003
private def e006 : Expr := .rat (49729 / 160000)
private def e007 : Expr := .mul e005 e006
private def e008 : Expr := .mul e007 e001
private def e009 : Expr := .rat (2229220599 / 2500000000)
private def e010 : Expr := .mul e009 e002
private def e011 : Expr := .sub e008 e010
private def e012 : Expr := .rat (-2104166991505918801 / 12500000000000000000)
private def e013 : Expr := .mul e012 e002
private def e014 : Expr := .mul e000 e001
private def e015 : Expr := .inv e014
private def e016 : Expr := .mul e013 e015
private def e017 : Expr := .rat (-70462623 / 500000000)
private def e018 : Expr := .sub e016 e017
private def e019 : Expr := .rat (209 / 200)
private def e020 : Expr := .mul e003 e019
private def e021 : Expr := .rat (159 / 200)
private def e022 : Expr := .mul e003 e021
private def e023 : Expr := .rat (-177 / 400)
private def e024 : Expr := .mul e022 e023
private def e025 : Expr := .add e020 e024
private def e026 : Expr := .rat (16725205953 / 32000000000)
private def e027 : Expr := .sub e025 e026
private def e028 : Expr := .rat (150685913 / 2500000000)
private def e029 : Expr := .rat (-100813601 / 1250000000)
private def e030 : Expr := .sub e029 e027

private theorem slope_checked : e011.positiveCheck=true := by decide +kernel
private theorem value_checked : e018.positiveCheck=true := by decide +kernel
private theorem gap_checked : e030.positiveCheck=true := by decide +kernel

theorem profile_lower : ((-70462623 / 500000000):ℝ)≤profile parameter (223 / 400) := by
  apply profile_lower_sqrt (u:=(5270779401 / 5000000000)) (by norm_num) (by norm_num) (by norm_num)
  · have h:=e011.positiveCheck_sound slope_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval,parameter] at h ⊢
    nlinarith
  · have h:=e018.positiveCheck_sound value_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv] at h ⊢
    ring_nf at h ⊢
    linarith

theorem gap_upper : positiveGap parameter (-((533857 / 200000):ℝ)) (223 / 400)≤(150685913 / 2500000000) := by
  apply gap_le_of_profile_lower profile_lower (by norm_num)
  have h:=e030.positiveCheck_sound gap_checked
  norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
  linarith

end Node22

namespace Node23
private def e000 : Expr := .rat (4051 / 7200)
private def e001 : Expr := .sqrt e000 (7500925868777059 / 10000000000000000) (375046293438853 / 500000000000000)
private def e002 : Expr := .exp (-2094087191 / 2000000000) (219358648400501 / 625000000000000) (3509738374408017 / 10000000000000000) { parts := 2, inner := (-2094087191 / 4000000000), terms := 32, innerLo := (296215224727225021845487 / 500000000000000000000000), innerHi := (23697217978178001747639 / 40000000000000000000000) }
private def e003 : Expr := .exp (-9 / 20) (1594070379054433 / 2500000000000000) (6376281516217733 / 10000000000000000) { parts := 1, inner := (-9 / 20), terms := 32, innerLo := (637628151621773293143743 / 1000000000000000000000000), innerHi := (9962939869090207705371 / 15625000000000000000000) }
private def e004 : Expr := .rat (21 / 10)
private def e005 : Expr := .mul e004 e003
private def e006 : Expr := .rat (16410601 / 51840000)
private def e007 : Expr := .mul e005 e006
private def e008 : Expr := .mul e007 e001
private def e009 : Expr := .rat (905912809 / 1000000000)
private def e010 : Expr := .mul e009 e002
private def e011 : Expr := .sub e008 e010
private def e012 : Expr := .rat (-291113972510270481 / 2000000000000000000)
private def e013 : Expr := .mul e012 e002
private def e014 : Expr := .mul e000 e001
private def e015 : Expr := .inv e014
private def e016 : Expr := .mul e013 e015
private def e017 : Expr := .rat (-1210495501 / 10000000000)
private def e018 : Expr := .sub e016 e017
private def e019 : Expr := .rat (209 / 200)
private def e020 : Expr := .mul e003 e019
private def e021 : Expr := .rat (159 / 200)
private def e022 : Expr := .mul e003 e021
private def e023 : Expr := .rat (-3149 / 7200)
private def e024 : Expr := .mul e022 e023
private def e025 : Expr := .add e020 e024
private def e026 : Expr := .rat (5293833317257 / 10368000000000)
private def e027 : Expr := .sub e025 e026
private def e028 : Expr := .rat (550728407 / 10000000000)
private def e029 : Expr := .rat (-329883547 / 5000000000)
private def e030 : Expr := .sub e029 e027

private theorem slope_checked : e011.positiveCheck=true := by decide +kernel
private theorem value_checked : e018.positiveCheck=true := by decide +kernel
private theorem gap_checked : e030.positiveCheck=true := by decide +kernel

theorem profile_lower : ((-1210495501 / 10000000000):ℝ)≤profile parameter (4051 / 7200) := by
  apply profile_lower_sqrt (u:=(2094087191 / 2000000000)) (by norm_num) (by norm_num) (by norm_num)
  · have h:=e011.positiveCheck_sound slope_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval,parameter] at h ⊢
    nlinarith
  · have h:=e018.positiveCheck_sound value_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv] at h ⊢
    ring_nf at h ⊢
    linarith

theorem gap_upper : positiveGap parameter (-((533857 / 200000):ℝ)) (4051 / 7200)≤(550728407 / 10000000000) := by
  apply gap_le_of_profile_lower profile_lower (by norm_num)
  have h:=e030.positiveCheck_sound gap_checked
  norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
  linarith

end Node23

namespace Node24
private def e000 : Expr := .rat (511 / 900)
private def e001 : Expr := .sqrt e000 (7535103036971543 / 10000000000000000) (941887879621443 / 1250000000000000)
private def e002 : Expr := .exp (-324974791 / 312500000) (3534831958739043 / 10000000000000000) (883707989684761 / 2500000000000000) { parts := 2, inner := (-324974791 / 625000000), terms := 32, innerLo := (118908905616678575170151 / 200000000000000000000000), innerHi := (148636132020848218962689 / 250000000000000000000000) }
private def e003 : Expr := .exp (-9 / 20) (1594070379054433 / 2500000000000000) (6376281516217733 / 10000000000000000) { parts := 1, inner := (-9 / 20), terms := 32, innerLo := (637628151621773293143743 / 1000000000000000000000000), innerHi := (9962939869090207705371 / 15625000000000000000000) }
private def e004 : Expr := .rat (21 / 10)
private def e005 : Expr := .mul e004 e003
private def e006 : Expr := .rat (261121 / 810000)
private def e007 : Expr := .mul e005 e006
private def e008 : Expr := .mul e007 e001
private def e009 : Expr := .rat (143775209 / 156250000)
private def e010 : Expr := .mul e009 e002
private def e011 : Expr := .sub e008 e010
private def e012 : Expr := .rat (-6003178691743681 / 48828125000000000)
private def e013 : Expr := .mul e012 e002
private def e014 : Expr := .mul e000 e001
private def e015 : Expr := .inv e014
private def e016 : Expr := .mul e013 e015
private def e017 : Expr := .rat (-1015809829 / 10000000000)
private def e018 : Expr := .sub e016 e017
private def e019 : Expr := .rat (209 / 200)
private def e020 : Expr := .mul e003 e019
private def e021 : Expr := .rat (159 / 200)
private def e022 : Expr := .mul e003 e021
private def e023 : Expr := .rat (-389 / 900)
private def e024 : Expr := .mul e022 e023
private def e025 : Expr := .add e020 e024
private def e026 : Expr := .rat (80783775097 / 162000000000)
private def e027 : Expr := .sub e025 e026
private def e028 : Expr := .rat (501374631 / 10000000000)
private def e029 : Expr := .rat (-257217599 / 5000000000)
private def e030 : Expr := .sub e029 e027

private theorem slope_checked : e011.positiveCheck=true := by decide +kernel
private theorem value_checked : e018.positiveCheck=true := by decide +kernel
private theorem gap_checked : e030.positiveCheck=true := by decide +kernel

theorem profile_lower : ((-1015809829 / 10000000000):ℝ)≤profile parameter (511 / 900) := by
  apply profile_lower_sqrt (u:=(324974791 / 312500000)) (by norm_num) (by norm_num) (by norm_num)
  · have h:=e011.positiveCheck_sound slope_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval,parameter] at h ⊢
    nlinarith
  · have h:=e018.positiveCheck_sound value_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv] at h ⊢
    ring_nf at h ⊢
    linarith

theorem gap_upper : positiveGap parameter (-((533857 / 200000):ℝ)) (511 / 900)≤(501374631 / 10000000000) := by
  apply gap_le_of_profile_lower profile_lower (by norm_num)
  have h:=e030.positiveCheck_sound gap_checked
  norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
  linarith

end Node24

#print axioms Node20.profile_lower
#print axioms Node24.gap_upper
end ForestUnimodality.SignedGaussian350JointData.AlphaFourNinthBeta65
