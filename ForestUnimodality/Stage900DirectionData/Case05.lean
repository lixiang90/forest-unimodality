import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.DirectionBudget
import ForestUnimodality.PointMassSqrtNormalization

namespace ForestUnimodality.Stage900DirectionData.Case05
open AnalyticNumericCertificate DirectionBudget
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def parameters : Parameters := {
  a := (17 / 20)
  b := (22 / 25)
  start := (240340909090909090909090909090909 / 1000000000000000000000000000000)
  alpha := (9 / 20)
  alpha1 := (1 / 4)
  vmin := (340 / 1369)
  vmax := (550 / 2209)
  eta := (3 / 37)
  R := (211213679 / 250000000)
  D := (1979584591032908783037620555107 / 500000000000000000000000000000)
  T := (19 / 10)
  rate0 := (32475932468941894671482343759 / 1000000000000000000000000000000)
  rate1 := (57752812364251340620374545241 / 1000000000000000000000000000000)
  c0 := (31 / 125)
  c1 := (51 / 200)
}

theorem parameters_valid : parameters.Valid := by
  constructor
  all_goals try norm_num [parameters, Parameters.A0, Parameters.A1]
  exact lt_trans (by norm_num : ((19 / 10) : ℝ) < 3) Real.pi_gt_three

private def e000 : Expr := .pi
private def e001 : Expr := .rat (240340909090909090909090909090909 / 1000000000000000000000000000000)
private def e002 : Expr := .sqrt e001 (155029322739573719 / 10000000000000000) (3875733068489343 / 250000000000000)
private def e003 : Expr := .rat (9 / 20)
private def e004 : Expr := .sqrt e003 (6708203932499369 / 10000000000000000) (670820393249937 / 1000000000000000)
private def e005 : Expr := .rat (2163068181818181818181818181818181 / 2143068181818181818181818181818181)
private def e006 : Expr := .sqrt e005 (627909606798103 / 625000000000000) (10046553708769649 / 10000000000000000)
private def e007 : Expr := .rat (340 / 1369)
private def e008 : Expr := .sqrt e007 (4983537544482641 / 10000000000000000) (2491768772241321 / 5000000000000000)
private def e009 : Expr := .rat 2
private def e010 : Expr := .mul e009 e000
private def e011 : Expr := .sqrt e010 (5013256549262001 / 2000000000000000) (12533141373155003 / 5000000000000000)
private def e012 : Expr := .mul e009 e000
private def e013 : Expr := .rat (550 / 2209)
private def e014 : Expr := .mul e012 e013
private def e015 : Expr := .sqrt e014 (12507583790796017 / 10000000000000000) (6253791895398009 / 5000000000000000)
private def e016 : Expr := .inv e015
private def e017 : Expr := .exp (-7805295133160466730702858755714201593097048278009575319786931 / 1000000000000000000000000000000000000000000000000000000000000) (4075711117441 / 10000000000000000) (2037855558721 / 5000000000000000) { parts := 8, inner := (-7805295133160466730702858755714201593097048278009575319786931 / 8000000000000000000000000000000000000000000000000000000000000), terms := 32, innerLo := (376942775701615923819557 / 1000000000000000000000000), innerHi := (188471387850807961909779 / 500000000000000000000000) }
private def e018 : Expr := .exp (-13880363426180861978646836725535790204289785068059943602314069 / 1000000000000000000000000000000000000000000000000000000000000) (9372053459 / 10000000000000000) (468602673 / 500000000000000) { parts := 14, inner := (-13880363426180861978646836725535790204289785068059943602314069 / 14000000000000000000000000000000000000000000000000000000000000), terms := 32, innerLo := (371036614287849434587553 / 1000000000000000000000000), innerHi := (185518307143924717293777 / 500000000000000000000000) }
private def e019 : Expr := .exp (-53732664509844817720010976287205935344211 / 120170454545454545454545454545454500000000) (3197281271599813 / 5000000000000000) (6394562543199627 / 10000000000000000) { parts := 1, inner := (-53732664509844817720010976287205935344211 / 120170454545454545454545454545454500000000), terms := 32, innerLo := (319728127159981318622137 / 500000000000000000000000), innerHi := (25578250172798505489771 / 40000000000000000000000) }
private def e020 : Expr := .rat (43 / 40)
private def e021 : Expr := .mul e020 e017
private def e022 : Expr := .sub e019 e021
private def e023 : Expr := .rat (2242251565459498169503323004022461 / 2163068181818181818181818181818181)
private def e024 : Expr := .mul e003 e004
private def e025 : Expr := .inv e024
private def e026 : Expr := .rat 1
private def e027 : Expr := .sub e025 e026
private def e028 : Expr := .rat (-33 / 40)
private def e029 : Expr := .add e027 e028
private def e030 : Expr := .rat (121 / 400)
private def e031 : Expr := .rat (400 / 121)
private def e032 : Expr := .mul e029 e031
private def e033 : Expr := .rat (3959169182065817566075241110214 / 240340909090909090909090909090909)
private def e034 : Expr := .mul e032 e033
private def e035 : Expr := .add e026 e034
private def e036 : Expr := .rat (14036591877582644628099173553718997645764462809917355371900826446283 / 169931425581095041322314049586776729751095041322314049586776859504157)
private def e037 : Expr := .rat 3
private def e038 : Expr := .mul e037 e000
private def e039 : Expr := .mul e038 e007
private def e040 : Expr := .mul e039 e002
private def e041 : Expr := .inv e040
private def e042 : Expr := .mul e036 e041
private def e043 : Expr := .mul e042 e023
private def e044 : Expr := .rat (4678863959194214876033057851239665881921487603305785123966942148761 / 4592741231921487603305785123966938641921487603305785123966942148761)
private def e045 : Expr := .mul e044 e006
private def e046 : Expr := .rat 16
private def e047 : Expr := .mul e046 e011
private def e048 : Expr := .mul e047 e007
private def e049 : Expr := .mul e048 e008
private def e050 : Expr := .mul e049 e001
private def e051 : Expr := .inv e050
private def e052 : Expr := .mul e045 e051
private def e053 : Expr := .mul e052 e035
private def e054 : Expr := .exp (-13274749431818181818181818181818176797 / 273800000000000000000000000000000000) 0 (1 / 10000000000000000) { parts := 49, inner := (-13274749431818181818181818181818176797 / 13416200000000000000000000000000000000), terms := 32, innerLo := (185889305463697965017489 / 500000000000000000000000), innerHi := (371778610927395930034979 / 1000000000000000000000000) }
private def e055 : Expr := .rat (19 / 10)
private def e056 : Expr := .inv e000
private def e057 : Expr := .mul e055 e056
private def e058 : Expr := .sub e026 e057
private def e059 : Expr := .mul e002 e058
private def e060 : Expr := .mul e059 e054
private def e061 : Expr := .rat (2907 / 13690)
private def e062 : Expr := .mul e000 e061
private def e063 : Expr := .mul e062 e002
private def e064 : Expr := .inv e063
private def e065 : Expr := .mul e054 e064
private def e066 : Expr := .mul e016 e022
private def e067 : Expr := .sub e066 e043
private def e068 : Expr := .sub e067 e053
private def e069 : Expr := .sub e068 e060
private def e070 : Expr := .sub e069 e065
private def e071 : Expr := .rat (42439 / 42500)
private def e072 : Expr := .inv e002
private def e073 : Expr := .mul e071 e072
private def e074 : Expr := .mul e073 e023
private def e075 : Expr := .rat (288859 / 153000)
private def e076 : Expr := .inv e002
private def e077 : Expr := .mul e075 e076
private def e078 : Expr := .mul e077 e017
private def e079 : Expr := .add e074 e078
private def e080 : Expr := .rat (236233909090909090909090909090909 / 1000000000000000000000000000000)
private def e081 : Expr := .inv e002
private def e082 : Expr := .mul e080 e081
private def e083 : Expr := .mul e082 e018
private def e084 : Expr := .add e079 e083
private def e085 : Expr := .rat (3 / 25)
private def e086 : Expr := .mul e085 e070
private def e087 : Expr := .rat (22 / 25)
private def e088 : Expr := .mul e087 e084
private def e089 : Expr := .sub e086 e088

def bracketExpression : Expr := e022
def massExpression : Expr := e070
def gradientExpression : Expr := e084
def marginExpression : Expr := e089

theorem bracket_checked : bracketExpression.positiveCheck = true := by decide +kernel
theorem mass_checked : massExpression.positiveCheck = true := by decide +kernel
theorem margin_checked : marginExpression.positiveCheck = true := by decide +kernel
theorem margin_expression_positive : 0 < marginExpression.eval :=
  marginExpression.positiveCheck_sound margin_checked

theorem bracket_eval : bracketExpression.eval =
    PointMassBudgetMonotonicity.mainBracket parameters.R parameters.D parameters.rate0 parameters.start := by
  norm_num [bracketExpression, Expr.eval, e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030, e031, e032, e033, e034, e035, e036, e037, e038, e039, e040, e041, e042, e043, e044, e045, e046, e047, e048, e049, e050, e051, e052, e053, e054, e055, e056, e057, e058, e059, e060, e061, e062, e063, e064, e065, e066, e067, e068, e069, e070, e071, e072, e073, e074, e075, e076, e077, e078, e079, e080, e081, e082, e083, e084, e085, e086, e087, e088, e089, parameters, PointMassBudgetMonotonicity.mainBracket]

theorem mass_eval : massExpression.eval = parameters.mass parameters.start := by
  unfold Parameters.mass PointMassBudgetMonotonicity.budget
  rw [PointMassSqrtNormalization.scaledError_eq_sqrtExpression
    parameters_valid.start_pos parameters_valid.alpha_pos parameters_valid.alpha_lt
    parameters_valid.cutoff_count parameters_valid.vmin_pos parameters_valid.T_pos]
  norm_num [massExpression, Expr.eval, e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030, e031, e032, e033, e034, e035, e036, e037, e038, e039, e040, e041, e042, e043, e044, e045, e046, e047, e048, e049, e050, e051, e052, e053, e054, e055, e056, e057, e058, e059, e060, e061, e062, e063, e064, e065, e066, e067, e068, e069, e070, e071, e072, e073, e074, e075, e076, e077, e078, e079, e080, e081, e082, e083, e084, e085, e086, e087, e088, e089, parameters, Parameters.H,
    PointMassBudgetMonotonicity.mainBracket, PointMassSqrtNormalization.sqrtExpression,
    PointMassSqrtNormalization.bThreeHalves, PointMassErrorEnvelope.rho]
  ring

theorem gradient_eval : gradientExpression.eval = parameters.gradient parameters.start := by
  norm_num [gradientExpression, Expr.eval, e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030, e031, e032, e033, e034, e035, e036, e037, e038, e039, e040, e041, e042, e043, e044, e045, e046, e047, e048, e049, e050, e051, e052, e053, e054, e055, e056, e057, e058, e059, e060, e061, e062, e063, e064, e065, e066, e067, e068, e069, e070, e071, e072, e073, e074, e075, e076, e077, e078, e079, e080, e081, e082, e083, e084, e085, e086, e087, e088, e089, parameters, Parameters.gradient,
    Parameters.A0, Parameters.A1, GradientBudgetMonotonicity.gradientCost, GradientBudgetMonotonicity.shiftedCost]
  ring

theorem margin_eval : marginExpression.eval = parameters.leftMargin parameters.start := by
  change (((3 / 25) : ℚ) : ℝ) * massExpression.eval -
    (((22 / 25) : ℚ) : ℝ) * gradientExpression.eval = _
  rw [mass_eval, gradient_eval]
  norm_num [Parameters.leftMargin, parameters]

theorem bracket_positive : 0 <
    PointMassBudgetMonotonicity.mainBracket parameters.R parameters.D parameters.rate0 parameters.start := by
  rw [← bracket_eval]
  exact bracketExpression.positiveCheck_sound bracket_checked

theorem mass_positive : 0 < parameters.mass parameters.start := by
  rw [← mass_eval]
  exact massExpression.positiveCheck_sound mass_checked

theorem margin_positive : 0 < parameters.leftMargin parameters.start := by
  rw [← margin_eval]
  exact margin_expression_positive

#print axioms parameters_valid
#print axioms mass_positive
#print axioms margin_positive
end ForestUnimodality.Stage900DirectionData.Case05
