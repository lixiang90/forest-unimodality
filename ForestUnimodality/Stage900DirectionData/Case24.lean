import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.DirectionBudget
import ForestUnimodality.PointMassSqrtNormalization

namespace ForestUnimodality.Stage900DirectionData.Case24
open AnalyticNumericCertificate DirectionBudget
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def parameters : Parameters := {
  a := (29 / 25)
  b := (6 / 5)
  start := (9452748354941381808581773248057 / 40000000000000000000000000000)
  alpha := (9 / 20)
  alpha1 := (1 / 4)
  vmin := (30 / 121)
  vmax := (725 / 2916)
  eta := (1 / 11)
  R := (23473887 / 25000000)
  D := (158322193391868473415189783253 / 40000000000000000000000000000)
  T := (19 / 10)
  rate0 := (34050640421730986561148940961 / 1000000000000000000000000000000)
  rate1 := (61008584455713445035681646907 / 1000000000000000000000000000000)
  c0 := (31 / 125)
  c1 := (51 / 200)
}

theorem parameters_valid : parameters.Valid := by
  constructor
  all_goals try norm_num [parameters, Parameters.A0, Parameters.A1]
  exact lt_trans (by norm_num : ((19 / 10) : ℝ) < 3) Real.pi_gt_three

private def e000 : Expr := .pi
private def e001 : Expr := .rat (9452748354941381808581773248057 / 40000000000000000000000000000)
private def e002 : Expr := .sqrt e001 (76863305431384901 / 5000000000000000) (153726610862769803 / 10000000000000000)
private def e003 : Expr := .rat (9 / 20)
private def e004 : Expr := .sqrt e003 (6708203932499369 / 10000000000000000) (670820393249937 / 1000000000000000)
private def e005 : Expr := .rat (85074735194472436277235959232513 / 84274735194472436277235959232513)
private def e006 : Expr := .sqrt e005 (10047351700596239 / 10000000000000000) (125591896257453 / 125000000000000)
private def e007 : Expr := .rat (30 / 121)
private def e008 : Expr := .sqrt e007 (4979295977319691 / 10000000000000000) (1244823994329923 / 2500000000000000)
private def e009 : Expr := .rat 2
private def e010 : Expr := .mul e009 e000
private def e011 : Expr := .sqrt e010 (5013256549262001 / 2000000000000000) (12533141373155003 / 5000000000000000)
private def e012 : Expr := .mul e009 e000
private def e013 : Expr := .rat (725 / 2916)
private def e014 : Expr := .mul e012 e013
private def e015 : Expr := .sqrt e014 (12498709601028839 / 10000000000000000) (312467740025721 / 250000000000000)
private def e016 : Expr := .inv e015
private def e017 : Expr := .exp (-321872135231218102510273522313065433131114073716626700962777 / 40000000000000000000000000000000000000000000000000000000000) (400154502387 / 1250000000000000) (3201236019097 / 10000000000000000) { parts := 9, inner := (-107290711743739367503424507437688477710371357905542233654259 / 120000000000000000000000000000000000000000000000000000000000), terms := 32, innerLo := (8179598031655625633489 / 20000000000000000000000), innerHi := (408979901582781281674451 / 1000000000000000000000000) }
private def e018 : Expr := .exp (-576698796351047625030642540223912266745382921838108397809699 / 40000000000000000000000000000000000000000000000000000000000) (5477373743 / 10000000000000000) (342335859 / 625000000000000) { parts := 15, inner := (-192232932117015875010214180074637422248460973946036132603233 / 200000000000000000000000000000000000000000000000000000000000), terms := 32, innerLo := (76489441061248368880129 / 200000000000000000000000), innerHi := (191223602653120922200323 / 500000000000000000000000) }
private def e019 : Expr := .exp (-77922303742573341234881136409495995853 / 157545805915689696809696220800950000000) (1524535527592379 / 2500000000000000) (6098142110369517 / 10000000000000000) { parts := 1, inner := (-77922303742573341234881136409495995853 / 157545805915689696809696220800950000000), terms := 32, innerLo := (609814211036951603744269 / 1000000000000000000000000), innerHi := (60981421103695160374427 / 100000000000000000000000) }
private def e020 : Expr := .rat (43 / 40)
private def e021 : Expr := .mul e020 e017
private def e022 : Expr := .sub e019 e021
private def e023 : Expr := .rat (88241179062309805745539754897573 / 85074735194472436277235959232513)
private def e024 : Expr := .mul e003 e004
private def e025 : Expr := .inv e024
private def e026 : Expr := .rat 1
private def e027 : Expr := .sub e025 e026
private def e028 : Expr := .rat (-33 / 40)
private def e029 : Expr := .add e027 e028
private def e030 : Expr := .rat (121 / 400)
private def e031 : Expr := .rat (400 / 121)
private def e032 : Expr := .mul e029 e031
private def e033 : Expr := .rat (158322193391868473415189783253 / 9452748354941381808581773248057)
private def e034 : Expr := .mul e032 e033
private def e035 : Expr := .add e026 e034
private def e036 : Expr := .rat (657973688037236999999999999996117679314251283173419102181481379 / 7102230992098451101956422465185273672456764114907610123996295169)
private def e037 : Expr := .rat 3
private def e038 : Expr := .mul e037 e000
private def e039 : Expr := .mul e038 e007
private def e040 : Expr := .mul e039 e002
private def e041 : Expr := .inv e040
private def e042 : Expr := .mul e036 e041
private def e043 : Expr := .mul e042 e023
private def e044 : Expr := .rat (7237710568409606999999999999957294472456764114907610123996295169 / 7102230992098451101956422465185273672456764114907610123996295169)
private def e045 : Expr := .mul e044 e006
private def e046 : Expr := .rat 16
private def e047 : Expr := .mul e046 e011
private def e048 : Expr := .mul e047 e007
private def e049 : Expr := .mul e048 e008
private def e050 : Expr := .mul e049 e001
private def e051 : Expr := .inv e050
private def e052 : Expr := .mul e045 e051
private def e053 : Expr := .mul e052 e035
private def e054 : Expr := .exp (-8375994383237604408022413077164689 / 176000000000000000000000000000000) 0 (1 / 10000000000000000) { parts := 48, inner := (-2791998127745868136007471025721563 / 2816000000000000000000000000000000), terms := 32, innerLo := (92757105711515311345603 / 250000000000000000000000), innerHi := (371028422846061245382413 / 1000000000000000000000000) }
private def e055 : Expr := .rat (19 / 10)
private def e056 : Expr := .inv e000
private def e057 : Expr := .mul e055 e056
private def e058 : Expr := .sub e026 e057
private def e059 : Expr := .mul e002 e058
private def e060 : Expr := .mul e059 e054
private def e061 : Expr := .rat (513 / 2420)
private def e062 : Expr := .mul e000 e061
private def e063 : Expr := .mul e062 e002
private def e064 : Expr := .inv e063
private def e065 : Expr := .mul e054 e064
private def e066 : Expr := .mul e016 e022
private def e067 : Expr := .sub e066 e043
private def e068 : Expr := .sub e067 e053
private def e069 : Expr := .sub e068 e060
private def e070 : Expr := .sub e069 e065
private def e071 : Expr := .rat (3751 / 3750)
private def e072 : Expr := .inv e002
private def e073 : Expr := .mul e071 e072
private def e074 : Expr := .mul e073 e023
private def e075 : Expr := .rat (25531 / 13500)
private def e076 : Expr := .inv e002
private def e077 : Expr := .mul e075 e076
private def e078 : Expr := .mul e077 e017
private def e079 : Expr := .add e074 e078
private def e080 : Expr := .rat (9288188354941381808581773248057 / 40000000000000000000000000000)
private def e081 : Expr := .inv e002
private def e082 : Expr := .mul e080 e081
private def e083 : Expr := .mul e082 e018
private def e084 : Expr := .add e079 e083
private def e085 : Expr := .rat (4 / 25)
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
  ring

theorem gradient_eval : gradientExpression.eval = parameters.gradient parameters.start := by
  norm_num [gradientExpression, Expr.eval, e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, e016, e017, e018, e019, e020, e021, e022, e023, e024, e025, e026, e027, e028, e029, e030, e031, e032, e033, e034, e035, e036, e037, e038, e039, e040, e041, e042, e043, e044, e045, e046, e047, e048, e049, e050, e051, e052, e053, e054, e055, e056, e057, e058, e059, e060, e061, e062, e063, e064, e065, e066, e067, e068, e069, e070, e071, e072, e073, e074, e075, e076, e077, e078, e079, e080, e081, e082, e083, e084, e085, e086, e087, parameters, Parameters.gradient,
    Parameters.A0, Parameters.A1, GradientBudgetMonotonicity.gradientCost, GradientBudgetMonotonicity.shiftedCost]
  ring

theorem margin_eval : marginExpression.eval = parameters.rightMargin parameters.start := by
  change (((4 / 25) : ℚ) : ℝ) * massExpression.eval -
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
end ForestUnimodality.Stage900DirectionData.Case24
