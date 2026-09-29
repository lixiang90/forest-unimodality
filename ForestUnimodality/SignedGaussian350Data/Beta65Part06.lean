import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.SignedGaussian350Profile

namespace ForestUnimodality.SignedGaussian350Data.Beta65
open AnalyticNumericCertificate SignedGaussian350Profile SignedGaussianProfile SignedGaussianHermite
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Node30
private def e000 : Expr := .rat (23 / 40)
private def e001 : Expr := .sqrt e000 (151657508881031 / 200000000000000) (7582875444051551 / 10000000000000000)
private def e002 : Expr := .exp (-10298881973 / 10000000000) (714093754285213 / 2000000000000000) (1785234385713033 / 5000000000000000) { parts := 2, inner := (-10298881973 / 20000000000), terms := 32, innerLo := (597533996641702854733403 / 1000000000000000000000000), innerHi := (149383499160425713683351 / 250000000000000000000000) }
private def e003 : Expr := .exp (-9 / 20) (1594070379054433 / 2500000000000000) (6376281516217733 / 10000000000000000) { parts := 1, inner := (-9 / 20), terms := 32, innerLo := (637628151621773293143743 / 1000000000000000000000000), innerHi := (9962939869090207705371 / 15625000000000000000000) }
private def e004 : Expr := .rat (21 / 10)
private def e005 : Expr := .mul e004 e003
private def e006 : Expr := .rat (529 / 1600)
private def e007 : Expr := .mul e005 e006
private def e008 : Expr := .mul e007 e001
private def e009 : Expr := .rat (4701118027 / 5000000000)
private def e010 : Expr := .mul e009 e002
private def e011 : Expr := .sub e008 e010
private def e012 : Expr := .rat (-4572560028784372729 / 50000000000000000000)
private def e013 : Expr := .mul e012 e002
private def e014 : Expr := .mul e000 e001
private def e015 : Expr := .inv e014
private def e016 : Expr := .mul e013 e015
private def e017 : Expr := .rat (-187220281 / 2500000000)
private def e018 : Expr := .sub e016 e017
private def e019 : Expr := .rat (209 / 200)
private def e020 : Expr := .mul e003 e019
private def e021 : Expr := .rat (159 / 200)
private def e022 : Expr := .mul e003 e021
private def e023 : Expr := .rat (-17 / 40)
private def e024 : Expr := .mul e022 e023
private def e025 : Expr := .add e020 e024
private def e026 : Expr := .rat (154284673 / 320000000)
private def e027 : Expr := .sub e025 e026
private def e028 : Expr := .rat (436313161 / 10000000000)
private def e029 : Expr := .rat (-312567963 / 10000000000)
private def e030 : Expr := .sub e029 e027

private theorem slope_checked : e011.positiveCheck=true := by decide +kernel
private theorem value_checked : e018.positiveCheck=true := by decide +kernel
private theorem gap_checked : e030.positiveCheck=true := by decide +kernel

theorem profile_lower : ((-187220281 / 2500000000):ℝ)≤profile parameter (23 / 40) := by
  apply profile_lower_sqrt (u:=(10298881973 / 10000000000)) (by norm_num) (by norm_num) (by norm_num)
  · have h:=e011.positiveCheck_sound slope_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval,parameter] at h ⊢
    nlinarith
  · have h:=e018.positiveCheck_sound value_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv] at h ⊢
    ring_nf at h ⊢
    linarith

theorem gap_upper : positiveGap parameter (-((533857 / 200000):ℝ)) (23 / 40)≤(436313161 / 10000000000) := by
  apply gap_le_of_profile_lower profile_lower (by norm_num)
  have h:=e030.positiveCheck_sound gap_checked
  norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
  linarith

end Node30

namespace Node31
private def e000 : Expr := .rat (233 / 400)
private def e001 : Expr := .sqrt e000 (3816084380618437 / 5000000000000000) (12211470017979 / 16000000000000)
private def e002 : Expr := .exp (-10194503481 / 10000000000) (14431727853921 / 40000000000000) (3607931963480251 / 10000000000000000) { parts := 2, inner := (-10194503481 / 20000000000), terms := 32, innerLo := (150165158314941905308679 / 250000000000000000000000), innerHi := (600660633259767621234717 / 1000000000000000000000000) }
private def e003 : Expr := .exp (-9 / 20) (1594070379054433 / 2500000000000000) (6376281516217733 / 10000000000000000) { parts := 1, inner := (-9 / 20), terms := 32, innerLo := (637628151621773293143743 / 1000000000000000000000000), innerHi := (9962939869090207705371 / 15625000000000000000000) }
private def e004 : Expr := .rat (21 / 10)
private def e005 : Expr := .mul e004 e003
private def e006 : Expr := .rat (54289 / 160000)
private def e007 : Expr := .mul e005 e006
private def e008 : Expr := .mul e007 e001
private def e009 : Expr := .rat (4805496519 / 5000000000)
private def e010 : Expr := .mul e009 e002
private def e011 : Expr := .sub e008 e010
private def e012 : Expr := .rat (-2955383819121117361 / 50000000000000000000)
private def e013 : Expr := .mul e012 e002
private def e014 : Expr := .mul e000 e001
private def e015 : Expr := .inv e014
private def e016 : Expr := .mul e013 e015
private def e017 : Expr := .rat (-1873779 / 39062500)
private def e018 : Expr := .sub e016 e017
private def e019 : Expr := .rat (209 / 200)
private def e020 : Expr := .mul e003 e019
private def e021 : Expr := .rat (159 / 200)
private def e022 : Expr := .mul e003 e021
private def e023 : Expr := .rat (-167 / 400)
private def e024 : Expr := .mul e022 e023
private def e025 : Expr := .add e020 e024
private def e026 : Expr := .rat (14888737873 / 32000000000)
private def e027 : Expr := .sub e025 e026
private def e028 : Expr := .rat (186901743 / 5000000000)
private def e029 : Expr := .rat (-52941969 / 5000000000)
private def e030 : Expr := .sub e029 e027

private theorem slope_checked : e011.positiveCheck=true := by decide +kernel
private theorem value_checked : e018.positiveCheck=true := by decide +kernel
private theorem gap_checked : e030.positiveCheck=true := by decide +kernel

theorem profile_lower : ((-1873779 / 39062500):ℝ)≤profile parameter (233 / 400) := by
  apply profile_lower_sqrt (u:=(10194503481 / 10000000000)) (by norm_num) (by norm_num) (by norm_num)
  · have h:=e011.positiveCheck_sound slope_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval,parameter] at h ⊢
    nlinarith
  · have h:=e018.positiveCheck_sound value_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv] at h ⊢
    ring_nf at h ⊢
    linarith

theorem gap_upper : positiveGap parameter (-((533857 / 200000):ℝ)) (233 / 400)≤(186901743 / 5000000000) := by
  apply gap_le_of_profile_lower profile_lower (by norm_num)
  have h:=e030.positiveCheck_sound gap_checked
  norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
  linarith

end Node31

namespace Node32
private def e000 : Expr := .rat (59 / 100)
private def e001 : Expr := .sqrt e000 (120017902310447 / 156250000000000) (7681145747868609 / 10000000000000000)
private def e002 : Expr := .exp (-10089935917 / 10000000000) (3645857170884677 / 10000000000000000) (1822928585442339 / 5000000000000000) { parts := 2, inner := (-10089935917 / 20000000000), terms := 32, innerLo := (603809338358117570202139 / 1000000000000000000000000), innerHi := (30190466917905878510107 / 50000000000000000000000) }
private def e003 : Expr := .exp (-9 / 20) (1594070379054433 / 2500000000000000) (6376281516217733 / 10000000000000000) { parts := 1, inner := (-9 / 20), terms := 32, innerLo := (637628151621773293143743 / 1000000000000000000000000), innerHi := (9962939869090207705371 / 15625000000000000000000) }
private def e004 : Expr := .rat (21 / 10)
private def e005 : Expr := .mul e004 e003
private def e006 : Expr := .rat (3481 / 10000)
private def e007 : Expr := .mul e005 e006
private def e008 : Expr := .mul e007 e001
private def e009 : Expr := .rat (4910064083 / 5000000000)
private def e010 : Expr := .mul e009 e002
private def e011 : Expr := .sub e008 e010
private def e012 : Expr := .rat (-1357127224166630889 / 50000000000000000000)
private def e013 : Expr := .mul e012 e002
private def e014 : Expr := .mul e000 e001
private def e015 : Expr := .inv e014
private def e016 : Expr := .mul e013 e015
private def e017 : Expr := .rat (-852967 / 39062500)
private def e018 : Expr := .sub e016 e017
private def e019 : Expr := .rat (209 / 200)
private def e020 : Expr := .mul e003 e019
private def e021 : Expr := .rat (159 / 200)
private def e022 : Expr := .mul e003 e021
private def e023 : Expr := .rat (-41 / 100)
private def e024 : Expr := .mul e022 e023
private def e025 : Expr := .add e020 e024
private def e026 : Expr := .rat (897413617 / 2000000000)
private def e027 : Expr := .sub e025 e026
private def e028 : Expr := .rat (316156693 / 10000000000)
private def e029 : Expr := .rat (97797141 / 10000000000)
private def e030 : Expr := .sub e029 e027

private theorem slope_checked : e011.positiveCheck=true := by decide +kernel
private theorem value_checked : e018.positiveCheck=true := by decide +kernel
private theorem gap_checked : e030.positiveCheck=true := by decide +kernel

theorem profile_lower : ((-852967 / 39062500):ℝ)≤profile parameter (59 / 100) := by
  apply profile_lower_sqrt (u:=(10089935917 / 10000000000)) (by norm_num) (by norm_num) (by norm_num)
  · have h:=e011.positiveCheck_sound slope_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval,parameter] at h ⊢
    nlinarith
  · have h:=e018.positiveCheck_sound value_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv] at h ⊢
    ring_nf at h ⊢
    linarith

theorem gap_upper : positiveGap parameter (-((533857 / 200000):ℝ)) (59 / 100)≤(316156693 / 10000000000) := by
  apply gap_le_of_profile_lower profile_lower (by norm_num)
  have h:=e030.positiveCheck_sound gap_checked
  norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
  linarith

end Node32

namespace Node33
private def e000 : Expr := .rat (239 / 400)
private def e001 : Expr := .sqrt e000 (7729812416870153 / 10000000000000000) (3864906208435077 / 5000000000000000)
private def e002 : Expr := .exp (-9985202577 / 10000000000) (3684242109018469 / 10000000000000000) (368424210901847 / 1000000000000000) { parts := 1, inner := (-9985202577 / 10000000000), terms := 32, innerLo := (368424210901846980691539 / 1000000000000000000000000), innerHi := (18421210545092349034577 / 50000000000000000000000) }
private def e003 : Expr := .exp (-9 / 20) (1594070379054433 / 2500000000000000) (6376281516217733 / 10000000000000000) { parts := 1, inner := (-9 / 20), terms := 32, innerLo := (637628151621773293143743 / 1000000000000000000000000), innerHi := (9962939869090207705371 / 15625000000000000000000) }
private def e004 : Expr := .rat (21 / 10)
private def e005 : Expr := .mul e004 e003
private def e006 : Expr := .rat (57121 / 160000)
private def e007 : Expr := .mul e005 e006
private def e008 : Expr := .mul e007 e001
private def e009 : Expr := .rat (5014797423 / 5000000000)
private def e010 : Expr := .mul e009 e002
private def e011 : Expr := .sub e008 e010
private def e012 : Expr := .rat (221742381272559071 / 50000000000000000000)
private def e013 : Expr := .mul e012 e002
private def e014 : Expr := .mul e000 e001
private def e015 : Expr := .inv e014
private def e016 : Expr := .mul e013 e015
private def e017 : Expr := .rat (35376917 / 10000000000)
private def e018 : Expr := .sub e016 e017
private def e019 : Expr := .rat (209 / 200)
private def e020 : Expr := .mul e003 e019
private def e021 : Expr := .rat (159 / 200)
private def e022 : Expr := .mul e003 e021
private def e023 : Expr := .rat (-161 / 400)
private def e024 : Expr := .mul e022 e023
private def e025 : Expr := .add e020 e024
private def e026 : Expr := .rat (13838107297 / 32000000000)
private def e027 : Expr := .sub e025 e026
private def e028 : Expr := .rat (263098357 / 10000000000)
private def e029 : Expr := .rat (149237637 / 5000000000)
private def e030 : Expr := .sub e029 e027

private theorem slope_checked : e011.positiveCheck=true := by decide +kernel
private theorem value_checked : e018.positiveCheck=true := by decide +kernel
private theorem gap_checked : e030.positiveCheck=true := by decide +kernel

theorem profile_lower : ((35376917 / 10000000000):ℝ)≤profile parameter (239 / 400) := by
  apply profile_lower_sqrt (u:=(9985202577 / 10000000000)) (by norm_num) (by norm_num) (by norm_num)
  · have h:=e011.positiveCheck_sound slope_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval,parameter] at h ⊢
    nlinarith
  · have h:=e018.positiveCheck_sound value_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv] at h ⊢
    ring_nf at h ⊢
    linarith

theorem gap_upper : positiveGap parameter (-((533857 / 200000):ℝ)) (239 / 400)≤(263098357 / 10000000000) := by
  apply gap_le_of_profile_lower profile_lower (by norm_num)
  have h:=e030.positiveCheck_sound gap_checked
  norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
  linarith

end Node33

namespace Node34
private def e000 : Expr := .rat (121 / 200)
private def e001 : Expr := .sqrt e000 (3889087296526011 / 5000000000000000) (7778174593052023 / 10000000000000000)
private def e002 : Expr := .exp (-9880325867 / 10000000000) (1861542277757643 / 5000000000000000) (3723084555515287 / 10000000000000000) { parts := 1, inner := (-9880325867 / 10000000000), terms := 32, innerLo := (93077113887882172047257 / 250000000000000000000000), innerHi := (372308455551528688189029 / 1000000000000000000000000) }
private def e003 : Expr := .exp (-9 / 20) (1594070379054433 / 2500000000000000) (6376281516217733 / 10000000000000000) { parts := 1, inner := (-9 / 20), terms := 32, innerLo := (637628151621773293143743 / 1000000000000000000000000), innerHi := (9962939869090207705371 / 15625000000000000000000) }
private def e004 : Expr := .rat (21 / 10)
private def e005 : Expr := .mul e004 e003
private def e006 : Expr := .rat (14641 / 40000)
private def e007 : Expr := .mul e005 e006
private def e008 : Expr := .mul e007 e001
private def e009 : Expr := .rat (5119674133 / 5000000000)
private def e010 : Expr := .mul e009 e002
private def e011 : Expr := .sub e008 e010
private def e012 : Expr := .rat (1780790096890698311 / 50000000000000000000)
private def e013 : Expr := .mul e012 e002
private def e014 : Expr := .mul e000 e001
private def e015 : Expr := .inv e014
private def e016 : Expr := .mul e013 e015
private def e017 : Expr := .rat (70445389 / 2500000000)
private def e018 : Expr := .sub e016 e017
private def e019 : Expr := .rat (209 / 200)
private def e020 : Expr := .mul e003 e019
private def e021 : Expr := .rat (159 / 200)
private def e022 : Expr := .mul e003 e021
private def e023 : Expr := .rat (-79 / 200)
private def e024 : Expr := .mul e022 e023
private def e025 : Expr := .add e020 e024
private def e026 : Expr := .rat (3331801537 / 8000000000)
private def e027 : Expr := .sub e025 e026
private def e028 : Expr := .rat (107184453 / 5000000000)
private def e029 : Expr := .rat (248075231 / 5000000000)
private def e030 : Expr := .sub e029 e027

private theorem slope_checked : e011.positiveCheck=true := by decide +kernel
private theorem value_checked : e018.positiveCheck=true := by decide +kernel
private theorem gap_checked : e030.positiveCheck=true := by decide +kernel

theorem profile_lower : ((70445389 / 2500000000):ℝ)≤profile parameter (121 / 200) := by
  apply profile_lower_sqrt (u:=(9880325867 / 10000000000)) (by norm_num) (by norm_num) (by norm_num)
  · have h:=e011.positiveCheck_sound slope_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval,parameter] at h ⊢
    nlinarith
  · have h:=e018.positiveCheck_sound value_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv] at h ⊢
    ring_nf at h ⊢
    linarith

theorem gap_upper : positiveGap parameter (-((533857 / 200000):ℝ)) (121 / 200)≤(107184453 / 5000000000) := by
  apply gap_le_of_profile_lower profile_lower (by norm_num)
  have h:=e030.positiveCheck_sound gap_checked
  norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
  linarith

end Node34

#print axioms Node30.profile_lower
#print axioms Node34.gap_upper
end ForestUnimodality.SignedGaussian350Data.Beta65
