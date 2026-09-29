import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.SignedGaussian350Profile

namespace ForestUnimodality.SignedGaussian350JointData.AlphaFourNinthBeta65
open AnalyticNumericCertificate SignedGaussian350Profile SignedGaussianProfile SignedGaussianHermite
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Node30
private def e000 : Expr := .rat (431 / 720)
private def e001 : Expr := .sqrt e000 (7736996258956773 / 10000000000000000) (3868498129478387 / 5000000000000000)
private def e002 : Expr := .exp (-9969673803 / 10000000000) (3689967729768647 / 10000000000000000) (461245966221081 / 1250000000000000) { parts := 1, inner := (-9969673803 / 10000000000), terms := 32, innerLo := (368996772976864797823931 / 1000000000000000000000000), innerHi := (92249193244216199455983 / 250000000000000000000000) }
private def e003 : Expr := .exp (-9 / 20) (1594070379054433 / 2500000000000000) (6376281516217733 / 10000000000000000) { parts := 1, inner := (-9 / 20), terms := 32, innerLo := (637628151621773293143743 / 1000000000000000000000000), innerHi := (9962939869090207705371 / 15625000000000000000000) }
private def e004 : Expr := .rat (21 / 10)
private def e005 : Expr := .mul e004 e003
private def e006 : Expr := .rat (185761 / 518400)
private def e007 : Expr := .mul e005 e006
private def e008 : Expr := .mul e007 e001
private def e009 : Expr := .rat (5030326197 / 5000000000)
private def e010 : Expr := .mul e009 e002
private def e011 : Expr := .sub e008 e010
private def e012 : Expr := .rat (453973276775517191 / 50000000000000000000)
private def e013 : Expr := .mul e012 e002
private def e014 : Expr := .mul e000 e001
private def e015 : Expr := .inv e014
private def e016 : Expr := .mul e013 e015
private def e017 : Expr := .rat (9042233 / 1250000000)
private def e018 : Expr := .sub e016 e017
private def e019 : Expr := .rat (209 / 200)
private def e020 : Expr := .mul e003 e019
private def e021 : Expr := .rat (159 / 200)
private def e022 : Expr := .mul e003 e021
private def e023 : Expr := .rat (-289 / 720)
private def e024 : Expr := .mul e022 e023
private def e025 : Expr := .add e020 e024
private def e026 : Expr := .rat (44588270497 / 103680000000)
private def e027 : Expr := .sub e025 e026
private def e028 : Expr := .rat (255612109 / 10000000000)
private def e029 : Expr := .rat (327949973 / 10000000000)
private def e030 : Expr := .sub e029 e027

private theorem slope_checked : e011.positiveCheck=true := by decide +kernel
private theorem value_checked : e018.positiveCheck=true := by decide +kernel
private theorem gap_checked : e030.positiveCheck=true := by decide +kernel

theorem profile_lower : ((9042233 / 1250000000):ℝ)≤profile parameter (431 / 720) := by
  apply profile_lower_sqrt (u:=(9969673803 / 10000000000)) (by norm_num) (by norm_num) (by norm_num)
  · have h:=e011.positiveCheck_sound slope_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval,parameter] at h ⊢
    nlinarith
  · have h:=e018.positiveCheck_sound value_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv] at h ⊢
    ring_nf at h ⊢
    linarith

theorem gap_upper : positiveGap parameter (-((533857 / 200000):ℝ)) (431 / 720)≤(255612109 / 10000000000) := by
  apply gap_le_of_profile_lower profile_lower (by norm_num)
  have h:=e030.positiveCheck_sound gap_checked
  norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
  linarith

end Node30

namespace Node31
private def e000 : Expr := .rat (483 / 800)
private def e001 : Expr := .sqrt e000 (3885067566980013 / 5000000000000000) (7770135133960027 / 10000000000000000)
private def e002 : Expr := .exp (-197956287 / 200000000) (3716579135573973 / 10000000000000000) (1858289567786987 / 5000000000000000) { parts := 1, inner := (-197956287 / 200000000), terms := 32, innerLo := (185828956778698652836437 / 500000000000000000000000), innerHi := (2973263308459178445383 / 8000000000000000000000) }
private def e003 : Expr := .exp (-9 / 20) (1594070379054433 / 2500000000000000) (6376281516217733 / 10000000000000000) { parts := 1, inner := (-9 / 20), terms := 32, innerLo := (637628151621773293143743 / 1000000000000000000000000), innerHi := (9962939869090207705371 / 15625000000000000000000) }
private def e004 : Expr := .rat (21 / 10)
private def e005 : Expr := .mul e004 e003
private def e006 : Expr := .rat (233289 / 640000)
private def e007 : Expr := .mul e005 e006
private def e008 : Expr := .mul e007 e001
private def e009 : Expr := .rat (102043713 / 100000000)
private def e010 : Expr := .mul e009 e002
private def e011 : Expr := .sub e008 e010
private def e012 : Expr := .rat (608937137173631 / 20000000000000000)
private def e013 : Expr := .mul e012 e002
private def e014 : Expr := .mul e000 e001
private def e015 : Expr := .inv e014
private def e016 : Expr := .mul e013 e015
private def e017 : Expr := .rat (241212679 / 10000000000)
private def e018 : Expr := .sub e016 e017
private def e019 : Expr := .rat (209 / 200)
private def e020 : Expr := .mul e003 e019
private def e021 : Expr := .rat (159 / 200)
private def e022 : Expr := .mul e003 e021
private def e023 : Expr := .rat (-317 / 800)
private def e024 : Expr := .mul e022 e023
private def e025 : Expr := .add e020 e024
private def e026 : Expr := .rat (53646756073 / 128000000000)
private def e027 : Expr := .sub e025 e026
private def e028 : Expr := .rat (27775057 / 1250000000)
private def e029 : Expr := .rat (92682627 / 2000000000)
private def e030 : Expr := .sub e029 e027

private theorem slope_checked : e011.positiveCheck=true := by decide +kernel
private theorem value_checked : e018.positiveCheck=true := by decide +kernel
private theorem gap_checked : e030.positiveCheck=true := by decide +kernel

theorem profile_lower : ((241212679 / 10000000000):ℝ)≤profile parameter (483 / 800) := by
  apply profile_lower_sqrt (u:=(197956287 / 200000000)) (by norm_num) (by norm_num) (by norm_num)
  · have h:=e011.positiveCheck_sound slope_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval,parameter] at h ⊢
    nlinarith
  · have h:=e018.positiveCheck_sound value_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv] at h ⊢
    ring_nf at h ⊢
    linarith

theorem gap_upper : positiveGap parameter (-((533857 / 200000):ℝ)) (483 / 800)≤(27775057 / 1250000000) := by
  apply gap_le_of_profile_lower profile_lower (by norm_num)
  have h:=e030.positiveCheck_sound gap_checked
  norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
  linarith

end Node31

namespace Node32
private def e000 : Expr := .rat (137 / 225)
private def e001 : Expr := .sqrt e000 (7803133273813083 / 10000000000000000) (1950783318453271 / 2500000000000000)
private def e002 : Expr := .exp (-4912948031 / 5000000000) (1871702241233669 / 5000000000000000) (3743404482467339 / 10000000000000000) { parts := 1, inner := (-4912948031 / 5000000000), terms := 32, innerLo := (46792556030841725889281 / 125000000000000000000000), innerHi := (374340448246733807114249 / 1000000000000000000000000) }
private def e003 : Expr := .exp (-9 / 20) (1594070379054433 / 2500000000000000) (6376281516217733 / 10000000000000000) { parts := 1, inner := (-9 / 20), terms := 32, innerLo := (637628151621773293143743 / 1000000000000000000000000), innerHi := (9962939869090207705371 / 15625000000000000000000) }
private def e004 : Expr := .rat (21 / 10)
private def e005 : Expr := .mul e004 e003
private def e006 : Expr := .rat (18769 / 50625)
private def e007 : Expr := .mul e005 e006
private def e008 : Expr := .mul e007 e001
private def e009 : Expr := .rat (2587051969 / 2500000000)
private def e010 : Expr := .mul e009 e002
private def e011 : Expr := .sub e008 e010
private def e012 : Expr := .rat (645311722193223039 / 12500000000000000000)
private def e013 : Expr := .mul e012 e002
private def e014 : Expr := .mul e000 e001
private def e015 : Expr := .inv e014
private def e016 : Expr := .mul e013 e015
private def e017 : Expr := .rat (406742189 / 10000000000)
private def e018 : Expr := .sub e016 e017
private def e019 : Expr := .rat (209 / 200)
private def e020 : Expr := .mul e003 e019
private def e021 : Expr := .rat (159 / 200)
private def e022 : Expr := .mul e003 e021
private def e023 : Expr := .rat (-88 / 225)
private def e024 : Expr := .mul e022 e023
private def e025 : Expr := .add e020 e024
private def e026 : Expr := .rat (64596697 / 158203125)
private def e027 : Expr := .sub e025 e026
private def e028 : Expr := .rat (2980067 / 156250000)
private def e029 : Expr := .rat (597466477 / 10000000000)
private def e030 : Expr := .sub e029 e027

private theorem slope_checked : e011.positiveCheck=true := by decide +kernel
private theorem value_checked : e018.positiveCheck=true := by decide +kernel
private theorem gap_checked : e030.positiveCheck=true := by decide +kernel

theorem profile_lower : ((406742189 / 10000000000):ℝ)≤profile parameter (137 / 225) := by
  apply profile_lower_sqrt (u:=(4912948031 / 5000000000)) (by norm_num) (by norm_num) (by norm_num)
  · have h:=e011.positiveCheck_sound slope_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval,parameter] at h ⊢
    nlinarith
  · have h:=e018.positiveCheck_sound value_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv] at h ⊢
    ring_nf at h ⊢
    linarith

theorem gap_upper : positiveGap parameter (-((533857 / 200000):ℝ)) (137 / 225)≤(2980067 / 156250000) := by
  apply gap_le_of_profile_lower profile_lower (by norm_num)
  have h:=e030.positiveCheck_sound gap_checked
  norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
  linarith

end Node32

namespace Node33
private def e000 : Expr := .rat (4421 / 7200)
private def e001 : Expr := .sqrt e000 (122437382132267 / 156250000000000) (7835992456465089 / 10000000000000000)
private def e002 : Expr := .exp (-1950785137 / 2000000000) (3770443087874661 / 10000000000000000) (1885221543937331 / 5000000000000000) { parts := 1, inner := (-1950785137 / 2000000000), terms := 32, innerLo := (94261077196866545863353 / 250000000000000000000000), innerHi := (377044308787466183453413 / 1000000000000000000000000) }
private def e003 : Expr := .exp (-9 / 20) (1594070379054433 / 2500000000000000) (6376281516217733 / 10000000000000000) { parts := 1, inner := (-9 / 20), terms := 32, innerLo := (637628151621773293143743 / 1000000000000000000000000), innerHi := (9962939869090207705371 / 15625000000000000000000) }
private def e004 : Expr := .rat (21 / 10)
private def e005 : Expr := .mul e004 e003
private def e006 : Expr := .rat (19545241 / 51840000)
private def e007 : Expr := .mul e005 e006
private def e008 : Expr := .mul e007 e001
private def e009 : Expr := .rat (1049214863 / 1000000000)
private def e010 : Expr := .mul e009 e002
private def e011 : Expr := .sub e008 e010
private def e012 : Expr := .rat (145222486259891231 / 2000000000000000000)
private def e013 : Expr := .mul e012 e002
private def e014 : Expr := .mul e000 e001
private def e015 : Expr := .inv e014
private def e016 : Expr := .mul e013 e015
private def e017 : Expr := .rat (569002577 / 10000000000)
private def e018 : Expr := .sub e016 e017
private def e019 : Expr := .rat (209 / 200)
private def e020 : Expr := .mul e003 e019
private def e021 : Expr := .rat (159 / 200)
private def e022 : Expr := .mul e003 e021
private def e023 : Expr := .rat (-2779 / 7200)
private def e024 : Expr := .mul e022 e023
private def e025 : Expr := .add e020 e024
private def e026 : Expr := .rat (4122892727737 / 10368000000000)
private def e027 : Expr := .sub e025 e026
private def e028 : Expr := .rat (5034607 / 312500000)
private def e029 : Expr := .rat (730110001 / 10000000000)
private def e030 : Expr := .sub e029 e027

private theorem slope_checked : e011.positiveCheck=true := by decide +kernel
private theorem value_checked : e018.positiveCheck=true := by decide +kernel
private theorem gap_checked : e030.positiveCheck=true := by decide +kernel

theorem profile_lower : ((569002577 / 10000000000):ℝ)≤profile parameter (4421 / 7200) := by
  apply profile_lower_sqrt (u:=(1950785137 / 2000000000)) (by norm_num) (by norm_num) (by norm_num)
  · have h:=e011.positiveCheck_sound slope_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval,parameter] at h ⊢
    nlinarith
  · have h:=e018.positiveCheck_sound value_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv] at h ⊢
    ring_nf at h ⊢
    linarith

theorem gap_upper : positiveGap parameter (-((533857 / 200000):ℝ)) (4421 / 7200)≤(5034607 / 312500000) := by
  apply gap_le_of_profile_lower profile_lower (by norm_num)
  have h:=e030.positiveCheck_sound gap_checked
  norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
  linarith

end Node33

namespace Node34
private def e000 : Expr := .rat (743 / 1200)
private def e001 : Expr := .sqrt e000 (7868714422741917 / 10000000000000000) (3934357211370959 / 5000000000000000)
private def e002 : Expr := .exp (-4840954891 / 5000000000) (3797694282435137 / 10000000000000000) (1898847141217569 / 5000000000000000) { parts := 1, inner := (-4840954891 / 5000000000), terms := 32, innerLo := (94942357060878439609199 / 250000000000000000000000), innerHi := (379769428243513758436797 / 1000000000000000000000000) }
private def e003 : Expr := .exp (-9 / 20) (1594070379054433 / 2500000000000000) (6376281516217733 / 10000000000000000) { parts := 1, inner := (-9 / 20), terms := 32, innerLo := (637628151621773293143743 / 1000000000000000000000000), innerHi := (9962939869090207705371 / 15625000000000000000000) }
private def e004 : Expr := .rat (21 / 10)
private def e005 : Expr := .mul e004 e003
private def e006 : Expr := .rat (552049 / 1440000)
private def e007 : Expr := .mul e005 e006
private def e008 : Expr := .mul e007 e001
private def e009 : Expr := .rat (2659045109 / 2500000000)
private def e010 : Expr := .mul e009 e002
private def e011 : Expr := .sub e008 e010
private def e012 : Expr := .rat (1167542970803178119 / 12500000000000000000)
private def e013 : Expr := .mul e012 e002
private def e014 : Expr := .mul e000 e001
private def e015 : Expr := .inv e014
private def e016 : Expr := .mul e013 e015
private def e017 : Expr := .rat (728067271 / 10000000000)
private def e018 : Expr := .sub e016 e017
private def e019 : Expr := .rat (209 / 200)
private def e020 : Expr := .mul e003 e019
private def e021 : Expr := .rat (159 / 200)
private def e022 : Expr := .mul e003 e021
private def e023 : Expr := .rat (-457 / 1200)
private def e024 : Expr := .mul e022 e023
private def e025 : Expr := .add e020 e024
private def e026 : Expr := .rat (111495500593 / 288000000000)
private def e027 : Expr := .sub e025 e026
private def e028 : Expr := .rat (66638217 / 5000000000)
private def e029 : Expr := .rat (172268741 / 2000000000)
private def e030 : Expr := .sub e029 e027

private theorem slope_checked : e011.positiveCheck=true := by decide +kernel
private theorem value_checked : e018.positiveCheck=true := by decide +kernel
private theorem gap_checked : e030.positiveCheck=true := by decide +kernel

theorem profile_lower : ((728067271 / 10000000000):ℝ)≤profile parameter (743 / 1200) := by
  apply profile_lower_sqrt (u:=(4840954891 / 5000000000)) (by norm_num) (by norm_num) (by norm_num)
  · have h:=e011.positiveCheck_sound slope_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval,parameter] at h ⊢
    nlinarith
  · have h:=e018.positiveCheck_sound value_checked
    norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv] at h ⊢
    ring_nf at h ⊢
    linarith

theorem gap_upper : positiveGap parameter (-((533857 / 200000):ℝ)) (743 / 1200)≤(66638217 / 5000000000) := by
  apply gap_le_of_profile_lower profile_lower (by norm_num)
  have h:=e030.positiveCheck_sound gap_checked
  norm_num [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030,Expr.eval] at h ⊢
  linarith

end Node34

#print axioms Node30.profile_lower
#print axioms Node34.gap_upper
end ForestUnimodality.SignedGaussian350JointData.AlphaFourNinthBeta65
