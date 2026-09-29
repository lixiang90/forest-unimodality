import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.DirectionBudget
import ForestUnimodality.PointMassSqrtNormalization

namespace ForestUnimodality.Stage900DirectionData.Case28
open AnalyticNumericCertificate DirectionBudget
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def parameters : Parameters := {
  a := (9 / 5)
  b := (9 / 4)
  start := (4074202648949134299448572890961 / 20000000000000000000000000000)
  alpha := (1 / 3)
  alpha1 := (1 / 4)
  vmin := (36 / 169)
  vmax := (45 / 196)
  eta := (5 / 13)
  R := (22914583 / 10000000)
  D := (7045326754076953980182272068053 / 1000000000000000000000000000000)
  T := (79 / 50)
  rate0 := (29912540352652810832540929313 / 1000000000000000000000000000000)
  rate1 := (4705053161130580215645833233 / 125000000000000000000000000000)
  c0 := (279 / 1000)
  c1 := (279 / 1000)
}

theorem parameters_valid : parameters.Valid := by
  constructor
  all_goals try norm_num [parameters, Parameters.A0, Parameters.A1]
  exact lt_trans (by norm_num : ((79 / 50) : ℝ) < 3) Real.pi_gt_three

private def e000 : Expr := .pi
private def e001 : Expr := .rat (4074202648949134299448572890961 / 20000000000000000000000000000)
private def e002 : Expr := .sqrt e001 (142727058558444591 / 10000000000000000) (8920441159902787 / 625000000000000)
private def e003 : Expr := .rat (1 / 3)
private def e004 : Expr := .sqrt e003 (5773502691896257 / 10000000000000000) (2886751345948129 / 5000000000000000)
private def e005 : Expr := .rat (1358067549649711433149524296987 / 1338067549649711433149524296987)
private def e006 : Expr := .sqrt e005 (10074457446956597 / 10000000000000000) (5037228723478299 / 5000000000000000)
private def e007 : Expr := .rat (36 / 169)
private def e008 : Expr := .sqrt e007 (923076923076923 / 2000000000000000) (576923076923077 / 1250000000000000)
private def e009 : Expr := .rat 2
private def e010 : Expr := .mul e009 e000
private def e011 : Expr := .sqrt e010 (5013256549262001 / 2000000000000000) (12533141373155003 / 5000000000000000)
private def e012 : Expr := .mul e009 e000
private def e013 : Expr := .rat (45 / 196)
private def e014 : Expr := .mul e012 e013
private def e015 : Expr := .sqrt e014 (12010695463709847 / 10000000000000000) (1501336932963731 / 1250000000000000)
private def e016 : Expr := .inv e015
private def e017 : Expr := .exp (-121869751141575953750923631877305803956978348502289957639793 / 20000000000000000000000000000000000000000000000000000000000) (22575219330607 / 10000000000000000) (1410951208163 / 625000000000000) { parts := 7, inner := (-121869751141575953750923631877305803956978348502289957639793 / 140000000000000000000000000000000000000000000000000000000000), terms := 32, innerLo := (418742870173218425794381 / 1000000000000000000000000), innerHi := (209371435086609212897191 / 500000000000000000000000) }
private def e018 : Expr := .exp (-19169340052524707924318631387108813864429920884020499106913 / 2500000000000000000000000000000000000000000000000000000000) (4676754334037 / 10000000000000000) (2338377167019 / 5000000000000000) { parts := 8, inner := (-19169340052524707924318631387108813864429920884020499106913 / 20000000000000000000000000000000000000000000000000000000000), terms := 32, innerLo := (47935038738547170692473 / 125000000000000000000000), innerHi := (76696061981675473107957 / 200000000000000000000000) }
private def e019 : Expr := .exp (-32528616936870324356990180327435861421 / 27161350992994228662990485939740000000) (3019159121219217 / 10000000000000000) (1509579560609609 / 5000000000000000) { parts := 2, inner := (-32528616936870324356990180327435861421 / 54322701985988457325980971879480000000), terms := 32, innerLo := (3434179715341433598877 / 6250000000000000000000), innerHi := (549468754454629375820321 / 1000000000000000000000000) }
private def e020 : Expr := .rat (43 / 40)
private def e021 : Expr := .mul e020 e017
private def e022 : Expr := .sub e019 e021
private def e023 : Expr := .rat (74948704236562525637658486917403 / 67903377482485571657476214849350)
private def e024 : Expr := .mul e003 e004
private def e025 : Expr := .inv e024
private def e026 : Expr := .rat 1
private def e027 : Expr := .sub e025 e026
private def e028 : Expr := .rat (-1)
private def e029 : Expr := .add e027 e028
private def e030 : Expr := .rat (4 / 9)
private def e031 : Expr := .rat (9 / 4)
private def e032 : Expr := .mul e029 e031
private def e033 : Expr := .rat (7045326754076953980182272068053 / 203710132447456714972428644548050)
private def e034 : Expr := .mul e032 e033
private def e035 : Expr := .add e026 e034
private def e036 : Expr := .rat (709364411312142857142857142852067357413784700050560222030065 / 1790424767425582971245447599535895129275840220131456577278169)
private def e037 : Expr := .rat 3
private def e038 : Expr := .mul e037 e000
private def e039 : Expr := .mul e038 e007
private def e040 : Expr := .mul e039 e002
private def e041 : Expr := .inv e040
private def e042 : Expr := .mul e036 e041
private def e043 : Expr := .mul e042 e023
private def e044 : Expr := .rat (1844347469411571428571428571415375129275840220131456577278169 / 1790424767425582971245447599535895129275840220131456577278169)
private def e045 : Expr := .mul e044 e006
private def e046 : Expr := .rat 16
private def e047 : Expr := .mul e046 e011
private def e048 : Expr := .mul e047 e007
private def e049 : Expr := .mul e048 e008
private def e050 : Expr := .mul e049 e001
private def e051 : Expr := .inv e050
private def e052 : Expr := .mul e045 e051
private def e053 : Expr := .mul e052 e035
private def e054 : Expr := .exp (-5867792015098049345275048479804831 / 325000000000000000000000000000000) (144186307 / 10000000000000000) (36046577 / 2500000000000000) { parts := 19, inner := (-5867792015098049345275048479804831 / 6175000000000000000000000000000000), terms := 32, innerLo := (386644458913268339190337 / 1000000000000000000000000), innerHi := (193322229456634169595169 / 500000000000000000000000) }
private def e055 : Expr := .rat (79 / 50)
private def e056 : Expr := .inv e000
private def e057 : Expr := .mul e055 e056
private def e058 : Expr := .sub e026 e057
private def e059 : Expr := .mul e002 e058
private def e060 : Expr := .mul e059 e054
private def e061 : Expr := .rat (474 / 4225)
private def e062 : Expr := .mul e000 e061
private def e063 : Expr := .mul e062 e002
private def e064 : Expr := .inv e063
private def e065 : Expr := .mul e054 e064
private def e066 : Expr := .mul e016 e022
private def e067 : Expr := .sub e066 e043
private def e068 : Expr := .sub e067 e053
private def e069 : Expr := .sub e068 e060
private def e070 : Expr := .sub e069 e065
private def e071 : Expr := .rat (5239 / 4000)
private def e072 : Expr := .inv e002
private def e073 : Expr := .mul e071 e072
private def e074 : Expr := .mul e073 e023
private def e075 : Expr := .inv e002
private def e076 : Expr := .mul e071 e075
private def e077 : Expr := .mul e076 e017
private def e078 : Expr := .add e074 e077
private def e079 : Expr := .rat (3969422648949134299448572890961 / 20000000000000000000000000000)
private def e080 : Expr := .inv e002
private def e081 : Expr := .mul e079 e080
private def e082 : Expr := .mul e081 e018
private def e083 : Expr := .add e078 e082
private def e084 : Expr := .rat (4 / 5)
private def e085 : Expr := .mul e084 e070
private def e086 : Expr := .sub e085 e083

def bracketExpression : Expr := e022
def massExpression : Expr := e070
def gradientExpression : Expr := e083
def marginExpression : Expr := e086

theorem bracket_checked : bracketExpression.positiveCheck = true := by decide +kernel
theorem mass_checked : massExpression.positiveCheck = true := by decide +kernel
theorem margin_checked : marginExpression.positiveCheck = true := by decide +kernel
theorem margin_expression_positive : 0 < marginExpression.eval :=
  marginExpression.positiveCheck_sound margin_checked

theorem bracket_eval : bracketExpression.eval =
    PointMassBudgetMonotonicity.mainBracket parameters.R parameters.D parameters.rate0 parameters.start := by
  norm_num [bracketExpression, Expr.eval, e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030, e031, e032, e033, e034, e035, e036, e037, e038, e039, e040, e041, e042, e043, e044, e045, e046, e047, e048, e049, e050, e051, e052, e053, e054, e055, e056, e057, e058, e059, e060, e061, e062, e063, e064, e065, e066, e067, e068, e069, e070, e071, e072, e073, e074, e075, e076, e077, e078, e079, e080, e081, e082, e083, e084, e085, e086, parameters, PointMassBudgetMonotonicity.mainBracket]

theorem mass_eval : massExpression.eval = parameters.mass parameters.start := by
  unfold Parameters.mass PointMassBudgetMonotonicity.budget
  rw [PointMassSqrtNormalization.scaledError_eq_sqrtExpression
    parameters_valid.start_pos parameters_valid.alpha_pos parameters_valid.alpha_lt
    parameters_valid.cutoff_count parameters_valid.vmin_pos parameters_valid.T_pos]
  norm_num [massExpression, Expr.eval, e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030, e031, e032, e033, e034, e035, e036, e037, e038, e039, e040, e041, e042, e043, e044, e045, e046, e047, e048, e049, e050, e051, e052, e053, e054, e055, e056, e057, e058, e059, e060, e061, e062, e063, e064, e065, e066, e067, e068, e069, e070, e071, e072, e073, e074, e075, e076, e077, e078, e079, e080, e081, e082, e083, e084, e085, e086, parameters, Parameters.H,
    PointMassBudgetMonotonicity.mainBracket, PointMassSqrtNormalization.sqrtExpression,
    PointMassSqrtNormalization.bThreeHalves, PointMassErrorEnvelope.rho]
  first | (solve | ring) | (ring_nf; simp only [inv_inv]; ring)

theorem gradient_eval : gradientExpression.eval = parameters.gradient parameters.start := by
  norm_num [gradientExpression, Expr.eval, e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030, e031, e032, e033, e034, e035, e036, e037, e038, e039, e040, e041, e042, e043, e044, e045, e046, e047, e048, e049, e050, e051, e052, e053, e054, e055, e056, e057, e058, e059, e060, e061, e062, e063, e064, e065, e066, e067, e068, e069, e070, e071, e072, e073, e074, e075, e076, e077, e078, e079, e080, e081, e082, e083, e084, e085, e086, parameters, Parameters.gradient,
    Parameters.A0, Parameters.A1, GradientBudgetMonotonicity.gradientCost, GradientBudgetMonotonicity.shiftedCost]
  first | (solve | ring) | (ring_nf; simp only [inv_inv]; ring)

theorem margin_eval : marginExpression.eval = parameters.rightMargin parameters.start := by
  change (((4 / 5) : ℚ) : ℝ) * massExpression.eval -
    gradientExpression.eval = _
  rw [mass_eval, gradient_eval]
  norm_num [Parameters.rightMargin, parameters]

theorem bracket_positive : 0 <
    PointMassBudgetMonotonicity.mainBracket parameters.R parameters.D parameters.rate0 parameters.start := by
  rw [← bracket_eval]
  exact bracketExpression.positiveCheck_sound bracket_checked

theorem mass_positive : 0 < parameters.mass parameters.start := by
  rw [← mass_eval]
  exact massExpression.positiveCheck_sound mass_checked

theorem margin_positive : 0 < parameters.rightMargin parameters.start := by
  rw [← margin_eval]
  exact margin_expression_positive

#print axioms parameters_valid
#print axioms mass_positive
#print axioms margin_positive
end ForestUnimodality.Stage900DirectionData.Case28
