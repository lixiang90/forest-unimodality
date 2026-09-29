import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.SignedGaussian350Profile

namespace ForestUnimodality.SignedGaussian350Data.Beta60
open AnalyticNumericCertificate SignedGaussian350Profile SignedGaussianProfile SignedGaussianHermite
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Node40
private def e000 : Expr := .rat (3 / 5)
private def e001 : Expr := .sqrt e000 (7745966692414833 / 10000000000000000) (3872983346207417 / 5000000000000000)
private def e002 : Expr := .exp (-4975129261 / 5000000000) (1848569432515873 / 5000000000000000) (3697138865031747 / 10000000000000000) { parts := 1, inner := (-4975129261 / 5000000000), terms := 32, innerLo := (369713886503174665286297 / 1000000000000000000000000), innerHi := (184856943251587332643149 / 500000000000000000000000) }
private def e003 : Expr := .exp (-9 / 20) (1594070379054433 / 2500000000000000) (6376281516217733 / 10000000000000000) { parts := 1, inner := (-9 / 20), terms := 32, innerLo := (637628151621773293143743 / 1000000000000000000000000), innerHi := (9962939869090207705371 / 15625000000000000000000) }
private def e004 : Expr := .rat (21 / 10)
private def e005 : Expr := .mul e004 e003
private def e006 : Expr := .rat (9 / 25)
private def e007 : Expr := .mul e005 e006
private def e008 : Expr := .mul e007 e001
private def e009 : Expr := .rat (2524870739 / 2500000000)
private def e010 : Expr := .mul e009 e002
private def e011 : Expr := .sub e008 e010
private def e012 : Expr := .rat (185911988841593879 / 12500000000000000000)
private def e013 : Expr := .mul e012 e002
private def e014 : Expr := .mul e000 e001
private def e015 : Expr := .inv e014
private def e016 : Expr := .mul e013 e015
private def e017 : Expr := .rat (23662807 / 2000000000)
private def e018 : Expr := .sub e016 e017
private def e019 : Expr := .rat (209 / 200)
private def e020 : Expr := .mul e003 e019
private def e021 : Expr := .rat (159 / 200)
private def e022 : Expr := .mul e003 e021
private def e023 : Expr := .mul e003 e019
private def e024 : Expr := .mul e003 e021
private def e025 : Expr := .rat (-2 / 5)
private def e026 : Expr := .mul e024 e025
private def e027 : Expr := .add e023 e026
private def e028 : Expr := .rat (1411639 / 3125000)
private def e029 : Expr := .sub e027 e028
private def e030 : Expr := .rat 0
private def e031 : Expr := .sub e017 e029

private theorem slope_checked : e011.positiveCheck=true := by decide +kernel
private theorem value_checked : e018.positiveCheck=true := by decide +kernel
private theorem gap_checked : e031.positiveCheck=true := by decide +kernel

theorem profile_lower : ((23662807 / 2000000000):ℝ)≤profile parameter (3 / 5) := by
  apply profile_lower_sqrt (u:=(4975129261 / 5000000000)) (by norm_num) (by norm_num) (by norm_num)
  · have h:=e011.positiveCheck_sound slope_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030, e031,Expr.eval,parameter] at h ⊢
    nlinarith
  · have h:=e018.positiveCheck_sound value_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030, e031,Expr.eval] at h ⊢
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv] at h ⊢
    ring_nf at h ⊢
    linarith

theorem gap_upper : positiveGap parameter (-((1411639 / 500000):ℝ)) (3 / 5)≤0 := by
  apply gap_le_of_profile_lower profile_lower (by norm_num)
  have h:=e031.positiveCheck_sound gap_checked
  norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030, e031,Expr.eval] at h ⊢
  linarith

theorem curvature_lower : -((1411639 / 500000):ℝ)≤coefficient parameter (3 / 5) := by
  apply SignedGaussian350Profile.coefficient_lower (by norm_num) (by norm_num) profile_lower
  have h:=e031.positiveCheck_sound gap_checked
  norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030, e031,Expr.eval] at h ⊢
  linarith

end Node40

#print axioms Node40.profile_lower
#print axioms Node40.gap_upper
end ForestUnimodality.SignedGaussian350Data.Beta60
