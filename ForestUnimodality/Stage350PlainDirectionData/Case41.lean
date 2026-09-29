import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.DirectionBudget
import ForestUnimodality.PointMassSqrtNormalization

namespace ForestUnimodality.Stage350PlainDirectionData.Case41
open AnalyticNumericCertificate DirectionBudget
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def parameters : Parameters := {
  a := (33 / 20)
  b := (9 / 5)
  start := (16792472406961991915060915823251 / 200000000000000000000000000000)
  alpha := (3 / 10)
  alpha1 := (1 / 10)
  vmin := (45 / 196)
  vmax := (660 / 2809)
  eta := (2 / 7)
  R := (43935559 / 25000000)
  D := (145571987196969696969696969697 / 62500000000000000000000000000)
  T := (177 / 100)
  rate0 := (263260157875846129 / 5000000000000000000)
  rate1 := (2259776768204540887 / 25000000000000000000)
  c0 := (31 / 100)
  c1 := (31 / 100)
}

theorem parameters_valid : parameters.Valid := by
  constructor
  all_goals try norm_num [parameters, Parameters.A0, Parameters.A1]
  exact lt_trans (by norm_num : ((177 / 100) : ℝ) < 3) Real.pi_gt_three

private def e000 : Expr := .pi
private def e001 : Expr := .rat (16792472406961991915060915823251 / 200000000000000000000000000000)
private def e002 : Expr := .sqrt e001 (91630978405127793 / 10000000000000000) (45815489202563897 / 5000000000000000)
private def e003 : Expr := .rat (3 / 10)
private def e004 : Expr := .sqrt e003 (5477225575051661 / 10000000000000000) (2738612787525831 / 5000000000000000)
private def e005 : Expr := .rat (50377417220885975745182747469753 / 48377417220885975745182747469753)
private def e006 : Expr := .sqrt e005 (63778841621521 / 62500000000000) (10204614659443361 / 10000000000000000)
private def e007 : Expr := .rat (45 / 196)
private def e008 : Expr := .sqrt e007 (4791574237499549 / 10000000000000000) (95831484749991 / 200000000000000)
private def e009 : Expr := .rat 2
private def e010 : Expr := .mul e009 e000
private def e011 : Expr := .sqrt e010 (5013256549262001 / 2000000000000000) (12533141373155003 / 5000000000000000)
private def e012 : Expr := .mul e009 e000
private def e013 : Expr := .rat (660 / 2809)
private def e014 : Expr := .mul e012 e013
private def e015 : Expr := .sqrt e014 (2430054579312701 / 2000000000000000) (6075136448281753 / 5000000000000000)
private def e016 : Expr := .inv e015
private def e017 : Expr := .exp (-4420788936982603838568640633128242433396236545379 / 1000000000000000000000000000000000000000000000000) (15030927222519 / 1250000000000000) (120247417780153 / 10000000000000000) { parts := 5, inner := (-4420788936982603838568640633128242433396236545379 / 5000000000000000000000000000000000000000000000000), terms := 32, innerLo := (6454092387064949421183 / 15625000000000000000000), innerHi := (413061912772156762955713 / 1000000000000000000000000) }
private def e018 : Expr := .exp (-37947239025968497989701517683779592414288094763637 / 5000000000000000000000000000000000000000000000000) (1264400637641 / 2500000000000000) (1011520510113 / 2000000000000000) { parts := 8, inner := (-37947239025968497989701517683779592414288094763637 / 40000000000000000000000000000000000000000000000000), terms := 32, innerLo := (96812870215187936890643 / 250000000000000000000000), innerHi := (387251480860751747562573 / 1000000000000000000000000) }
private def e019 : Expr := .exp (-772723939119223333814409128473757882309 / 839623620348099595753045791162550000000) (3983908099772041 / 10000000000000000) (1991954049886021 / 5000000000000000) { parts := 1, inner := (-772723939119223333814409128473757882309 / 839623620348099595753045791162550000000), terms := 32, innerLo := (398390809977204194420239 / 1000000000000000000000000), innerHi := (4979885124715052430253 / 12500000000000000000000) }
private def e020 : Expr := .rat (43 / 40)
private def e021 : Expr := .mul e020 e017
private def e022 : Expr := .sub e019 e021
private def e023 : Expr := .rat (55035720811189006048213050500057 / 50377417220885975745182747469753)
private def e024 : Expr := .mul e003 e004
private def e025 : Expr := .inv e024
private def e026 : Expr := .rat 1
private def e027 : Expr := .sub e025 e026
private def e028 : Expr := .rat (-21 / 20)
private def e029 : Expr := .add e027 e028
private def e030 : Expr := .rat (49 / 100)
private def e031 : Expr := .rat (100 / 49)
private def e032 : Expr := .mul e029 e031
private def e033 : Expr := .rat (2329151795151515151515151515152 / 83962362034809959575304579116255)
private def e034 : Expr := .mul e032 e033
private def e035 : Expr := .add e026 e034
private def e036 : Expr := .rat (5075768331694437735849056603760689094739351909839342247299762018 / 16382621478745724754606581184009327831587731684437697865549167063)
private def e037 : Expr := .rat 3
private def e038 : Expr := .mul e037 e000
private def e039 : Expr := .mul e038 e007
private def e040 : Expr := .mul e039 e002
private def e041 : Expr := .inv e040
private def e042 : Expr := .mul e036 e041
private def e043 : Expr := .mul e042 e023
private def e044 : Expr := .rat (2537884165847218867924528301880344547369675954919671123649881009 / 2340374496963674964943797312001332547369675954919671123649881009)
private def e045 : Expr := .mul e044 e006
private def e046 : Expr := .rat 16
private def e047 : Expr := .mul e046 e011
private def e048 : Expr := .mul e047 e007
private def e049 : Expr := .mul e048 e008
private def e050 : Expr := .mul e049 e001
private def e051 : Expr := .inv e050
private def e052 : Expr := .mul e045 e051
private def e053 : Expr := .mul e052 e035
private def e054 : Expr := .exp (-14204466937018230607087472659319025633 / 1568000000000000000000000000000000000) (581713006159 / 5000000000000000) (1163426012319 / 10000000000000000) { parts := 10, inner := (-14204466937018230607087472659319025633 / 15680000000000000000000000000000000000), terms := 32, innerLo := (202089561385691636009949 / 500000000000000000000000), innerHi := (404179122771383272019899 / 1000000000000000000000000) }
private def e055 : Expr := .rat (177 / 100)
private def e056 : Expr := .inv e000
private def e057 : Expr := .mul e055 e056
private def e058 : Expr := .sub e026 e057
private def e059 : Expr := .mul e002 e058
private def e060 : Expr := .mul e059 e054
private def e061 : Expr := .rat (4779 / 39200)
private def e062 : Expr := .mul e000 e061
private def e063 : Expr := .mul e062 e002
private def e064 : Expr := .inv e063
private def e065 : Expr := .mul e054 e064
private def e066 : Expr := .mul e016 e022
private def e067 : Expr := .sub e066 e043
private def e068 : Expr := .sub e067 e053
private def e069 : Expr := .sub e068 e060
private def e070 : Expr := .sub e069 e065
private def e071 : Expr := .rat (1519 / 1125)
private def e072 : Expr := .inv e002
private def e073 : Expr := .mul e071 e072
private def e074 : Expr := .mul e073 e023
private def e075 : Expr := .rat (6076 / 675)
private def e076 : Expr := .inv e002
private def e077 : Expr := .mul e075 e076
private def e078 : Expr := .mul e077 e017
private def e079 : Expr := .add e074 e078
private def e080 : Expr := .rat (126828251662657927235548242409259 / 1800000000000000000000000000000)
private def e081 : Expr := .inv e002
private def e082 : Expr := .mul e080 e081
private def e083 : Expr := .mul e082 e018
private def e084 : Expr := .add e079 e083
private def e085 : Expr := .rat (13 / 20)
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
  ring_nf; simp only [inv_inv]; ring

theorem gradient_eval : gradientExpression.eval = parameters.gradient parameters.start := by
  norm_num [gradientExpression, Expr.eval, e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030, e031, e032, e033, e034, e035, e036, e037, e038, e039, e040, e041, e042, e043, e044, e045, e046, e047, e048, e049, e050, e051, e052, e053, e054, e055, e056, e057, e058, e059, e060, e061, e062, e063, e064, e065, e066, e067, e068, e069, e070, e071, e072, e073, e074, e075, e076, e077, e078, e079, e080, e081, e082, e083, e084, e085, e086, e087, parameters, Parameters.gradient,
    Parameters.A0, Parameters.A1, GradientBudgetMonotonicity.gradientCost, GradientBudgetMonotonicity.shiftedCost]
  ring_nf; simp only [inv_inv]; ring

theorem margin_eval : marginExpression.eval = parameters.rightMargin parameters.start := by
  change (((13 / 20) : ℚ) : ℝ) * massExpression.eval -
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
end ForestUnimodality.Stage350PlainDirectionData.Case41
