import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.DirectionBudget
import ForestUnimodality.PointMassSqrtNormalization

namespace ForestUnimodality.Stage900DirectionData.Case25
open AnalyticNumericCertificate DirectionBudget
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def parameters : Parameters := {
  a := (6 / 5)
  b := (13 / 10)
  start := (4596722783746421937959337643287 / 20000000000000000000000000000)
  alpha := (9 / 20)
  alpha1 := (1 / 4)
  vmin := (130 / 529)
  vmax := (30 / 121)
  eta := (3 / 23)
  R := (14108033 / 12500000)
  D := (1092675022896714786798918550931 / 250000000000000000000000000000)
  T := (19 / 10)
  rate0 := (1955009174838756465889193663 / 62500000000000000000000000000)
  rate1 := (28129494143279467164548736943 / 500000000000000000000000000000)
  c0 := (261 / 1000)
  c1 := (279 / 1000)
}

theorem parameters_valid : parameters.Valid := by
  constructor
  all_goals try norm_num [parameters, Parameters.A0, Parameters.A1]
  exact lt_trans (by norm_num : ((19 / 10) : ℝ) < 3) Real.pi_gt_three

private def e000 : Expr := .pi
private def e001 : Expr := .rat (4596722783746421937959337643287 / 20000000000000000000000000000)
private def e002 : Expr := .sqrt e001 (1895043449317691 / 125000000000000) (151603475945415281 / 10000000000000000)
private def e003 : Expr := .rat (9 / 20)
private def e004 : Expr := .sqrt e003 (6708203932499369 / 10000000000000000) (670820393249937 / 1000000000000000)
private def e005 : Expr := .rat (41370505053717797441634038789583 / 40970505053717797441634038789583)
private def e006 : Expr := .sqrt e005 (5024348517574721 / 5000000000000000) (10048697035149443 / 10000000000000000)
private def e007 : Expr := .rat (130 / 529)
private def e008 : Expr := .sqrt e007 (4957284456952773 / 10000000000000000) (2478642228476387 / 5000000000000000)
private def e009 : Expr := .rat 2
private def e010 : Expr := .mul e009 e000
private def e011 : Expr := .sqrt e010 (5013256549262001 / 2000000000000000) (12533141373155003 / 5000000000000000)
private def e012 : Expr := .mul e009 e000
private def e013 : Expr := .rat (30 / 121)
private def e014 : Expr := .mul e012 e013
private def e015 : Expr := .sqrt e014 (624062204225297 / 500000000000000) (12481244084505941 / 10000000000000000)
private def e016 : Expr := .inv e015
private def e017 : Expr := .exp (-8986635216414603935152849022545885656520457284543154890281 / 1250000000000000000000000000000000000000000000000000000000) (60368880009 / 80000000000000) (3773055000563 / 5000000000000000) { parts := 8, inner := (-8986635216414603935152849022545885656520457284543154890281 / 10000000000000000000000000000000000000000000000000000000000), terms := 32, innerLo := (407113394556054289268557 / 1000000000000000000000000), innerHi := (203556697278027144634279 / 500000000000000000000000) }
private def e018 : Expr := .exp (-129303486623674264583624087051321431467952804124750132851641 / 10000000000000000000000000000000000000000000000000000000000) (24233766937 / 10000000000000000) (12116883469 / 5000000000000000) { parts := 13, inner := (-129303486623674264583624087051321431467952804124750132851641 / 130000000000000000000000000000000000000000000000000000000000), terms := 32, innerLo := (184927876743555881186983 / 500000000000000000000000), innerHi := (369855753487111762373967 / 1000000000000000000000000) }
private def e019 : Expr := .exp (-22709580597878842897683681260809408157 / 38306023197886849482994480360725000000) (221100718842967 / 400000000000000) (43183734149017 / 78125000000000) { parts := 1, inner := (-22709580597878842897683681260809408157 / 38306023197886849482994480360725000000), terms := 32, innerLo := (276375898553708754963441 / 500000000000000000000000), innerHi := (552751797107417509926883 / 1000000000000000000000000) }
private def e020 : Expr := .rat (43 / 40)
private def e021 : Expr := .mul e020 e017
private def e022 : Expr := .sub e019 e021
private def e023 : Expr := .rat (215593925451762705502561542355363 / 206852525268588987208170193947915)
private def e024 : Expr := .mul e003 e004
private def e025 : Expr := .inv e024
private def e026 : Expr := .rat 1
private def e027 : Expr := .sub e025 e026
private def e028 : Expr := .rat (-33 / 40)
private def e029 : Expr := .add e027 e028
private def e030 : Expr := .rat (121 / 400)
private def e031 : Expr := .rat (400 / 121)
private def e032 : Expr := .mul e029 e031
private def e033 : Expr := .rat (2185350045793429573597837101862 / 114918069593660548448983441082175)
private def e034 : Expr := .mul e032 e033
private def e035 : Expr := .add e026 e034
private def e036 : Expr := .rat (223241568052133454545454545453439049806328021943595896836867029 / 1678582284356715580228510950778032981848514834900901875749313889)
private def e037 : Expr := .rat 3
private def e038 : Expr := .mul e037 e000
private def e039 : Expr := .mul e038 e007
private def e040 : Expr := .mul e039 e002
private def e041 : Expr := .inv e040
private def e042 : Expr := .mul e036 e041
private def e043 : Expr := .mul e042 e023
private def e044 : Expr := .rat (1711518688399689818181818181809699381848514834900901875749313889 / 1678582284356715580228510950778032981848514834900901875749313889)
private def e045 : Expr := .mul e044 e006
private def e046 : Expr := .rat 16
private def e047 : Expr := .mul e046 e011
private def e048 : Expr := .mul e047 e007
private def e049 : Expr := .mul e048 e008
private def e050 : Expr := .mul e049 e001
private def e051 : Expr := .inv e050
private def e052 : Expr := .mul e045 e051
private def e053 : Expr := .mul e052 e035
private def e054 : Expr := .exp (-8441381748569461886677762784326653 / 184000000000000000000000000000000) 0 (1 / 10000000000000000) { parts := 46, inner := (-8441381748569461886677762784326653 / 8464000000000000000000000000000000), terms := 32, innerLo := (184431917973631257130757 / 500000000000000000000000), innerHi := (73772767189452502852303 / 200000000000000000000000) }
private def e055 : Expr := .rat (19 / 10)
private def e056 : Expr := .inv e000
private def e057 : Expr := .mul e055 e056
private def e058 : Expr := .sub e026 e057
private def e059 : Expr := .mul e002 e058
private def e060 : Expr := .mul e059 e054
private def e061 : Expr := .rat (2223 / 10580)
private def e062 : Expr := .mul e000 e061
private def e063 : Expr := .mul e062 e002
private def e064 : Expr := .inv e063
private def e065 : Expr := .mul e054 e064
private def e066 : Expr := .mul e016 e022
private def e067 : Expr := .sub e066 e043
private def e068 : Expr := .sub e067 e053
private def e069 : Expr := .sub e068 e060
private def e070 : Expr := .sub e069 e065
private def e071 : Expr := .rat (138069 / 130000)
private def e072 : Expr := .inv e002
private def e073 : Expr := .mul e071 e072
private def e074 : Expr := .mul e073 e023
private def e075 : Expr := .rat (35443 / 16250)
private def e076 : Expr := .inv e002
private def e077 : Expr := .mul e075 e076
private def e078 : Expr := .mul e077 e017
private def e079 : Expr := .add e074 e078
private def e080 : Expr := .rat (58576668188703485193471389362731 / 260000000000000000000000000000)
private def e081 : Expr := .inv e002
private def e082 : Expr := .mul e080 e081
private def e083 : Expr := .mul e082 e018
private def e084 : Expr := .add e079 e083
private def e085 : Expr := .rat (1 / 5)
private def e086 : Expr := .mul e085 e070
private def e087 : Expr := .sub e086 e084

def bracketExpression : Expr := e022
def massExpression : Expr := e070
def gradientExpression : Expr := e084
def marginExpression : Expr := e087

theorem bracket_checked : bracketExpression.positiveCheck = true := by decide +kernel
theorem mass_checked : massExpression.positiveCheck = true := by decide +kernel
theorem margin_checked : marginExpression.positiveCheck = true := by decide +kernel
theorem margin_expression_positive : 0 < marginExpression.eval :=
  marginExpression.positiveCheck_sound margin_checked

theorem bracket_eval : bracketExpression.eval =
    PointMassBudgetMonotonicity.mainBracket parameters.R parameters.D parameters.rate0 parameters.start := by
  norm_num [bracketExpression, Expr.eval, e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030, e031, e032, e033, e034, e035, e036, e037, e038, e039, e040, e041, e042, e043, e044, e045, e046, e047, e048, e049, e050, e051, e052, e053, e054, e055, e056, e057, e058, e059, e060, e061, e062, e063, e064, e065, e066, e067, e068, e069, e070, e071, e072, e073, e074, e075, e076, e077, e078, e079, e080, e081, e082, e083, e084, e085, e086, e087, parameters, PointMassBudgetMonotonicity.mainBracket]

theorem mass_eval : massExpression.eval = parameters.mass parameters.start := by
  unfold Parameters.mass PointMassBudgetMonotonicity.budget
  rw [PointMassSqrtNormalization.scaledError_eq_sqrtExpression
    parameters_valid.start_pos parameters_valid.alpha_pos parameters_valid.alpha_lt
    parameters_valid.cutoff_count parameters_valid.vmin_pos parameters_valid.T_pos]
  norm_num [massExpression, Expr.eval, e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030, e031, e032, e033, e034, e035, e036, e037, e038, e039, e040, e041, e042, e043, e044, e045, e046, e047, e048, e049, e050, e051, e052, e053, e054, e055, e056, e057, e058, e059, e060, e061, e062, e063, e064, e065, e066, e067, e068, e069, e070, e071, e072, e073, e074, e075, e076, e077, e078, e079, e080, e081, e082, e083, e084, e085, e086, e087, parameters, Parameters.H,
    PointMassBudgetMonotonicity.mainBracket, PointMassSqrtNormalization.sqrtExpression,
    PointMassSqrtNormalization.bThreeHalves, PointMassErrorEnvelope.rho]
  first | (solve | ring) | (ring_nf; simp only [inv_inv]; ring)

theorem gradient_eval : gradientExpression.eval = parameters.gradient parameters.start := by
  norm_num [gradientExpression, Expr.eval, e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030, e031, e032, e033, e034, e035, e036, e037, e038, e039, e040, e041, e042, e043, e044, e045, e046, e047, e048, e049, e050, e051, e052, e053, e054, e055, e056, e057, e058, e059, e060, e061, e062, e063, e064, e065, e066, e067, e068, e069, e070, e071, e072, e073, e074, e075, e076, e077, e078, e079, e080, e081, e082, e083, e084, e085, e086, e087, parameters, Parameters.gradient,
    Parameters.A0, Parameters.A1, GradientBudgetMonotonicity.gradientCost, GradientBudgetMonotonicity.shiftedCost]
  first | (solve | ring) | (ring_nf; simp only [inv_inv]; ring)

theorem margin_eval : marginExpression.eval = parameters.rightMargin parameters.start := by
  change (((1 / 5) : ℚ) : ℝ) * massExpression.eval -
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
end ForestUnimodality.Stage900DirectionData.Case25
