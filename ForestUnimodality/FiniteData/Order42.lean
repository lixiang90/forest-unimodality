import ForestUnimodality.KernelCertificate
import ForestUnimodality.FiniteWitness
import Mathlib.Tactic.IntervalCases

/-! Generated candidate witnesses. Each sign is rechecked by the Lean kernel.
The coverage theorem quantifies over Domain, independently of this record list.
Source and integer-witness hashes are recorded in research/finite-integer-witnesses/manifest.json.
-/
namespace ForestUnimodality.FiniteRows.FiniteData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_42_21_1_checked :
    (Witness.rising).check 42 21 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_21_2_checked :
    (Witness.rising).check 42 21 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_21_3_checked :
    (Witness.rising).check 42 21 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_21_4_checked :
    (Witness.rising).check 42 21 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_21_5_checked :
    (Witness.rising).check 42 21 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_21_6_checked :
    (Witness.rising).check 42 21 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_21_7_checked :
    (Witness.rising).check 42 21 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_21_8_checked :
    (Witness.rising).check 42 21 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_21_9_checked :
    (Witness.rising).check 42 21 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_21_10 : Certificate := {
  objectiveScale := 2574740124000000
  eta := 0
  rows := #[⟨.count 3, 3071465786036007360⟩, ⟨.count 4, 515256787635670080⟩, ⟨.count 5, 104310961591636800⟩, ⟨.count 6, 24601641884820000⟩, ⟨.count 7, 7232882714137080⟩, ⟨.count 8, 2886592647818880⟩, ⟨.count 9, 2588849699879520⟩, ⟨.path 10, 343271163589200⟩, ⟨.path 11, 600827311299600⟩, ⟨.privateRow 9 2, 55511397073440⟩, ⟨.privateRow 11 0, 54739826190000⟩, ⟨.privateRow 12 5, 109004197889664⟩, ⟨.hall 9 1, 79482227627880⟩, ⟨.hall 9 2, 4060131108264⟩, ⟨.hall 0 3, 94798326729506400⟩, ⟨.hall 1 3, 5313954647121120⟩, ⟨.hall 8 3, 10620568944216⟩, ⟨.hall 1 4, 500233384991340⟩, ⟨.hall 7 4, 5551139707344⟩, ⟨.hall 0 5, 7626508984294200⟩, ⟨.hall 1 5, 103873599069240⟩, ⟨.hall 7 5, 3389814421840⟩, ⟨.hall 6 7, 4076379278895⟩, ⟨.hall 6 8, 1660317267840⟩, ⟨.hall 5 11, 23159787415380⟩, ⟨.hall 4 15, 1894326425131140⟩]
  caps := #[0, 156827057294793600, 0, 2743167634590240, 721583422560000, 348397042593600, 196737082542000, 54025231019760, 36701817942240, 0, 25033284262800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_42_21_10_checked :
    (Witness.linear .positive case_42_21_10).check 42 21 10 = true := by
  change case_42_21_10.check 42 21 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_21_11 : Certificate := {
  objectiveScale := 33000000
  eta := 0
  rows := #[⟨.count 3, 70572902400⟩, ⟨.count 4, 13967553600⟩, ⟨.count 5, 3027024000⟩, ⟨.count 6, 762161400⟩, ⟨.count 7, 216936720⟩, ⟨.count 8, 74954880⟩, ⟨.count 9, 32931360⟩, ⟨.count 10, 33264000⟩, ⟨.path 12, 8567640⟩, ⟨.path 13, 1208760⟩, ⟨.privateRow 8 6, 1936935⟩, ⟨.privateRow 9 4, 1909600⟩, ⟨.privateRow 10 2, 249480⟩, ⟨.privateRow 12 0, 856548⟩, ⟨.privateRow 13 0, 911680⟩, ⟨.hall 10 1, 1353240⟩, ⟨.hall 9 3, 289296⟩, ⟨.hall 10 3, 33390⟩, ⟨.hall 0 5, 242342100⟩, ⟨.hall 1 5, 12792780⟩, ⟨.hall 8 5, 158760⟩, ⟨.hall 1 7, 623700⟩, ⟨.hall 7 7, 181440⟩, ⟨.hall 0 8, 6985440⟩, ⟨.hall 6 10, 423000⟩, ⟨.hall 6 11, 452430⟩, ⟨.hall 5 13, 7404540⟩, ⟨.hall 2 15, 900900⟩, ⟨.hall 2 16, 6246240⟩, ⟨.hall 4 16, 570810240⟩]
  caps := #[0, 3421345200, 316436640, 82265040, 25053600, 9094800, 1035720, 3483480, 0, 68640, 291720, 0, 2160, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_42_21_11_checked :
    (Witness.linear .positive case_42_21_11).check 42 21 11 = true := by
  change case_42_21_11.check 42 21 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_21_12 : Certificate := {
  objectiveScale := 12600000
  eta := 0
  rows := #[⟨.count 3, 69249660480⟩, ⟨.count 4, 15584849280⟩, ⟨.count 5, 4122518400⟩, ⟨.count 6, 1116215100⟩, ⟨.count 7, 351891540⟩, ⟨.count 8, 128288160⟩, ⟨.count 9, 56382480⟩, ⟨.count 10, 34511400⟩, ⟨.count 11, 34511400⟩, ⟨.path 13, 6713280⟩, ⟨.privateRow 4 17, 220540320⟩, ⟨.privateRow 9 5, 2058210⟩, ⟨.privateRow 9 6, 689040⟩, ⟨.privateRow 10 3, 249480⟩, ⟨.privateRow 13 0, 2143680⟩, ⟨.hall 11 1, 2564100⟩, ⟨.hall 10 2, 790440⟩, ⟨.hall 1 3, 720720⟩, ⟨.hall 10 3, 195930⟩, ⟨.hall 11 3, 23265⟩, ⟨.hall 0 4, 514594080⟩, ⟨.hall 1 4, 30450420⟩, ⟨.hall 9 4, 477414⟩, ⟨.hall 1 5, 2522520⟩, ⟨.hall 0 6, 35135100⟩, ⟨.hall 8 6, 382800⟩, ⟨.hall 7 8, 543410⟩, ⟨.hall 6 11, 3222450⟩, ⟨.hall 7 11, 391545⟩, ⟨.hall 5 13, 14032590⟩, ⟨.hall 4 16, 1166124960⟩, ⟨.assumptionRow 12, 34394220⟩]
  caps := #[0, 359770320, 0, 49008960, 0, 0, 0, 220500, 0, 0, 55440, 0, 89460, 20160, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_42_21_12_checked :
    (Witness.linear .conditional case_42_21_12).check 42 21 12 = true := by
  change case_42_21_12.check 42 21 12 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_21_13 : Certificate := {
  objectiveScale := 6720000
  eta := 0
  rows := #[⟨.count 2, 18716521824⟩, ⟨.count 3, 5425291872⟩, ⟨.count 4, 1666304640⟩, ⟨.count 5, 544864320⟩, ⟨.count 6, 192432240⟩, ⟨.count 7, 73657584⟩, ⟨.count 8, 31135104⟩, ⟨.count 9, 14170464⟩, ⟨.count 10, 6985440⟩, ⟨.count 11, 5987520⟩, ⟨.count 12, 4989600⟩, ⟨.count 14, 4036032⟩, ⟨.path 11, 1014840⟩, ⟨.privateRow 3 18, 632215584⟩, ⟨.privateRow 14 0, 333333⟩, ⟨.hall 0 1, 1676106432⟩, ⟨.hall 12 1, 554400⟩, ⟨.hall 11 2, 260568⟩, ⟨.hall 0 3, 29405376⟩, ⟨.hall 10 3, 100548⟩, ⟨.hall 11 3, 68112⟩, ⟨.hall 12 3, 7920⟩, ⟨.hall 10 4, 149760⟩, ⟨.hall 9 5, 219708⟩, ⟨.hall 8 6, 28632⟩, ⟨.hall 8 7, 242144⟩, ⟨.hall 7 9, 535248⟩, ⟨.hall 9 10, 340200⟩, ⟨.hall 7 11, 182952⟩, ⟨.hall 6 12, 7028208⟩, ⟨.hall 5 13, 8634912⟩, ⟨.hall 4 15, 68396328⟩, ⟨.hall 3 17, 999782784⟩, ⟨.assumptionRow 13, 4900896⟩]
  caps := #[0, 658144800, 56233008, 0, 2333760, 413952, 388080, 206304, 0, 0, 75240, 0, 0, 49056, 17304, 0, 0, 0, 0, 0, 0, 0] }

theorem case_42_21_13_checked :
    (Witness.linear .conditional case_42_21_13).check 42 21 13 = true := by
  change case_42_21_13.check 42 21 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_22_1_checked :
    (Witness.rising).check 42 22 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_22_2_checked :
    (Witness.rising).check 42 22 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_22_3_checked :
    (Witness.rising).check 42 22 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_22_4_checked :
    (Witness.rising).check 42 22 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_22_5_checked :
    (Witness.rising).check 42 22 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_22_6_checked :
    (Witness.rising).check 42 22 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_22_7_checked :
    (Witness.rising).check 42 22 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_22_8_checked :
    (Witness.rising).check 42 22 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_22_9 : Certificate := {
  objectiveScale := 54953711612800000
  eta := 1217202499933286106240
  rows := #[⟨.count 2, 267059013935901707520⟩, ⟨.count 3, 37563213906205827840⟩, ⟨.count 4, 5478599288495773440⟩, ⟨.count 5, 983726391580732800⟩, ⟨.count 6, 223230219627935520⟩, ⟨.count 7, 73779479368554960⟩, ⟨.count 8, 54716142490289280⟩, ⟨.count 10, 7937544848688000⟩, ⟨.path 9, 18463382770996800⟩, ⟨.path 10, 7667401515602400⟩, ⟨.privateRow 6 9, 7961247239555610⟩, ⟨.privateRow 6 10, 11440773968017680⟩, ⟨.privateRow 7 5, 958175056734480⟩, ⟨.privateRow 7 6, 3621410342632368⟩, ⟨.privateRow 7 7, 5194892116711440⟩, ⟨.privateRow 7 8, 5607780941016540⟩, ⟨.privateRow 8 2, 794772118823760⟩, ⟨.privateRow 8 3, 2000922763940100⟩, ⟨.privateRow 8 4, 264584828289600⟩, ⟨.privateRow 9 0, 533579403717360⟩, ⟨.hall 5 9, 12791509161795⟩, ⟨.hall 5 10, 4655247766650⟩, ⟨.hall 4 14, 662741762050368⟩, ⟨.hall 6 15, 2128254212554470⟩, ⟨.hall 3 18, 121870557013645440⟩]
  caps := #[0, 1077397865578157760, 79125280076556480, 43510743061144320, 7512296029226560, 8443896343136800, 0, 809057586604878, 237569122510720, 223521222379520, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_42_22_9_checked :
    (Witness.linear .positive case_42_22_9).check 42 22 9 = true := by
  change case_42_22_9.check 42 22 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_22_10 : Certificate := {
  objectiveScale := 1045687500
  eta := 34881171605280
  rows := #[⟨.count 2, 8545643346240⟩, ⟨.count 3, 1386365460480⟩, ⟨.count 4, 238281563520⟩, ⟨.count 5, 46589142600⟩, ⟨.count 6, 10830980160⟩, ⟨.count 7, 3026303280⟩, ⟨.count 8, 1225224000⟩, ⟨.count 9, 1029188160⟩, ⟨.path 10, 174388500⟩, ⟨.path 11, 221750100⟩, ⟨.privateRow 4 18, 9238188960⟩, ⟨.privateRow 6 10, 106186080⟩, ⟨.privateRow 7 7, 55621280⟩, ⟨.privateRow 7 8, 243185085⟩, ⟨.privateRow 7 9, 273049920⟩, ⟨.privateRow 8 4, 12252240⟩, ⟨.privateRow 8 5, 98017920⟩, ⟨.privateRow 8 6, 112312200⟩, ⟨.privateRow 8 7, 205225020⟩, ⟨.privateRow 9 2, 43563520⟩, ⟨.privateRow 9 3, 63117600⟩, ⟨.privateRow 9 4, 7351344⟩, ⟨.privateRow 10 0, 33158160⟩, ⟨.privateRow 11 0, 18378360⟩, ⟨.hall 11 1, 20420400⟩, ⟨.hall 12 1, 30630600⟩, ⟨.hall 6 8, 264537⟩, ⟨.hall 6 9, 827424⟩, ⟨.hall 5 11, 4129125⟩, ⟨.hall 7 14, 398197800⟩, ⟨.hall 4 15, 166045880⟩]
  caps := #[0, 19670971320, 3663419760, 898789320, 591608160, 13706550, 0, 0, 0, 24873212, 0, 1209780, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_42_22_10_checked :
    (Witness.linear .positive case_42_22_10).check 42 22 10 = true := by
  change case_42_22_10.check 42 22 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_22_11 : Certificate := {
  objectiveScale := 3702600000
  eta := 162723396195360
  rows := #[⟨.count 2, 44457840947520⟩, ⟨.count 3, 8404007451840⟩, ⟨.count 4, 1615139285760⟩, ⟨.count 5, 353783430000⟩, ⟨.count 6, 88681713120⟩, ⟨.count 7, 24528984480⟩, ⟨.count 8, 8418231360⟩, ⟨.count 9, 3701118960⟩, ⟨.count 10, 3760495200⟩, ⟨.path 12, 1028010060⟩, ⟨.path 13, 59376240⟩, ⟨.privateRow 4 18, 71700108480⟩, ⟨.privateRow 7 9, 1492147800⟩, ⟨.privateRow 8 6, 209649440⟩, ⟨.privateRow 8 7, 1029600495⟩, ⟨.privateRow 8 8, 1622479320⟩, ⟨.privateRow 9 4, 304798032⟩, ⟨.privateRow 9 5, 564440800⟩, ⟨.privateRow 9 6, 840613620⟩, ⟨.privateRow 9 7, 224624400⟩, ⟨.privateRow 10 2, 298680480⟩, ⟨.privateRow 10 3, 286985160⟩, ⟨.privateRow 11 0, 164934000⟩, ⟨.privateRow 12 0, 92363040⟩, ⟨.privateRow 13 0, 119742084⟩, ⟨.hall 7 8, 439824⟩, ⟨.hall 7 9, 12864852⟩, ⟨.hall 6 10, 29099070⟩, ⟨.hall 5 13, 277477200⟩, ⟨.hall 8 13, 3027245760⟩, ⟨.hall 4 16, 9545215680⟩]
  caps := #[0, 0, 0, 0, 8057598120, 1048576320, 721440720, 212336443, 19472684, 207032936, 0, 0, 25211340, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_42_22_11_checked :
    (Witness.linear .positive case_42_22_11).check 42 22 11 = true := by
  change case_42_22_11.check 42 22 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_22_12 : Certificate := {
  objectiveScale := 4813380000
  eta := 254663421012000
  rows := #[⟨.count 2, 73271580782400⟩, ⟨.count 3, 15786153583200⟩, ⟨.count 4, 3896604391680⟩, ⟨.count 5, 950498148600⟩, ⟨.count 6, 271570899600⟩, ⟨.count 7, 81471269880⟩, ⟨.count 8, 26415829440⟩, ⟨.count 9, 9703774080⟩, ⟨.count 10, 4778373600⟩, ⟨.count 11, 4851887040⟩, ⟨.path 13, 229270041⟩, ⟨.path 14, 916875960⟩, ⟨.privateRow 9 6, 1229818590⟩, ⟨.privateRow 10 6, 210038400⟩, ⟨.privateRow 11 4, 280269990⟩, ⟨.privateRow 12 0, 142942800⟩, ⟨.privateRow 13 0, 121297176⟩, ⟨.privateRow 14 0, 97337240⟩, ⟨.privateRow 15 6, 876035160⟩, ⟨.hall 11 3, 24504480⟩, ⟨.hall 10 4, 38705940⟩, ⟨.hall 12 4, 855712⟩, ⟨.hall 9 5, 50854650⟩, ⟨.hall 8 7, 51387600⟩, ⟨.hall 7 9, 91920972⟩, ⟨.hall 6 11, 192856092⟩, ⟨.hall 5 14, 1168046880⟩, ⟨.hall 4 16, 32934341440⟩]
  caps := #[0, 0, 0, 22251861918, 6194820060, 138705567, 1752070320, 0, 230240010, 494574795, 35006400, 90032085, 197377752, 0, 430189760, 0, 0, 0, 0, 0, 0] }

theorem case_42_22_12_checked :
    (Witness.linear .positive case_42_22_12).check 42 22 12 = true := by
  change case_42_22_12.check 42 22 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_22_13 : Certificate := {
  objectiveScale := 9302400000
  eta := 328438642371840
  rows := #[⟨.count 2, 85196489938560⟩, ⟨.count 3, 22328065599840⟩, ⟨.count 4, 6004185707520⟩, ⟨.count 5, 1815781968000⟩, ⟨.count 6, 578023926480⟩, ⟨.count 7, 195196561560⟩, ⟨.count 8, 71700108480⟩, ⟨.count 9, 30728617920⟩, ⟨.count 10, 12697776000⟩, ⟨.count 11, 11174042880⟩, ⟨.count 12, 9311702400⟩, ⟨.count 14, 9078909840⟩, ⟨.path 11, 1793627550⟩, ⟨.privateRow 3 19, 1166135530560⟩, ⟨.privateRow 8 8, 2261413440⟩, ⟨.privateRow 9 6, 892371480⟩, ⟨.privateRow 9 7, 7826264160⟩, ⟨.privateRow 9 8, 8561593040⟩, ⟨.privateRow 10 3, 184117752⟩, ⟨.privateRow 10 4, 35271600⟩, ⟨.privateRow 10 5, 3841077240⟩, ⟨.privateRow 10 6, 9015420960⟩, ⟨.privateRow 10 7, 8888443200⟩, ⟨.privateRow 11 3, 1883503440⟩, ⟨.privateRow 11 4, 4904515980⟩, ⟨.privateRow 11 5, 4371662880⟩, ⟨.privateRow 12 1, 1032047016⟩, ⟨.privateRow 12 2, 1707145440⟩, ⟨.privateRow 13 0, 558702144⟩, ⟨.hall 8 7, 51046920⟩, ⟨.hall 8 8, 209459040⟩, ⟨.hall 9 8, 26697888⟩, ⟨.hall 7 9, 428549940⟩, ⟨.hall 9 9, 271781244⟩, ⟨.hall 7 10, 14612520⟩, ⟨.hall 6 11, 1101746217⟩, ⟨.hall 5 13, 3932286930⟩, ⟨.hall 4 16, 156655699200⟩, ⟨.hall 3 18, 2323245244320⟩, ⟨.assumptionRow 13, 9151468560⟩]
  caps := #[0, 871667322120, 151922843280, 0, 1002817530, 7349593680, 786408480, 1662192675, 673272600, 210448332, 131048586, 0, 519019656, 0, 223490160, 0, 0, 0, 0, 0, 0] }

theorem case_42_22_13_checked :
    (Witness.linear .conditional case_42_22_13).check 42 22 13 = true := by
  change case_42_22_13.check 42 22 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_22_14 : Certificate := {
  objectiveScale := 93366000000
  eta := 2744808654107520
  rows := #[⟨.count 2, 714909676440960⟩, ⟨.count 3, 189531321819840⟩, ⟨.count 4, 54618721597440⟩, ⟨.count 5, 16205854064400⟩, ⟨.count 6, 4938926952960⟩, ⟨.count 7, 1543414672800⟩, ⟨.count 8, 541941079680⟩, ⟨.count 9, 201132771840⟩, ⟨.count 10, 68567990400⟩, ⟨.count 11, 41902660800⟩, ⟨.count 12, 39109150080⟩, ⟨.count 13, 36315639360⟩, ⟨.count 15, 90789098400⟩, ⟨.path 10, 22183761600⟩, ⟨.path 11, 2065055850⟩, ⟨.privateRow 3 19, 22225171288320⟩, ⟨.privateRow 9 7, 43898025600⟩, ⟨.privateRow 9 8, 94746571920⟩, ⟨.privateRow 10 5, 12666031560⟩, ⟨.privateRow 10 6, 69547533120⟩, ⟨.privateRow 10 7, 113454628560⟩, ⟨.privateRow 11 3, 1058148000⟩, ⟨.privateRow 11 4, 28808079300⟩, ⟨.privateRow 11 5, 76730846400⟩, ⟨.privateRow 11 6, 103296407760⟩, ⟨.privateRow 12 2, 6932045120⟩, ⟨.privateRow 12 3, 40564103580⟩, ⟨.privateRow 12 4, 43099879680⟩, ⟨.privateRow 13 1, 19476977520⟩, ⟨.privateRow 13 2, 4975940970⟩, ⟨.privateRow 14 0, 5476167840⟩, ⟨.hall 9 7, 1120008960⟩, ⟨.hall 8 8, 2743897920⟩, ⟨.hall 9 8, 3025977696⟩, ⟨.hall 8 9, 3670354944⟩, ⟨.hall 7 10, 11829489984⟩, ⟨.hall 10 11, 350776062000⟩, ⟨.hall 6 12, 43464033756⟩, ⟨.hall 7 12, 5254460640⟩, ⟨.hall 5 13, 50482362645⟩, ⟨.hall 4 15, 254802868320⟩, ⟨.hall 3 18, 32200504015680⟩, ⟨.assumptionRow 14, 40376136960⟩]
  caps := #[0, 13211598831480, 0, 0, 28757261520, 5043838800, 1854515520, 0, 1402521480, 0, 5862522960, 538532010, 4330262260, 4060497600, 0, 2576901600, 0, 0, 0, 0, 0] }

theorem case_42_22_14_checked :
    (Witness.linear .conditional case_42_22_14).check 42 22 14 = true := by
  change case_42_22_14.check 42 22 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_23_1_checked :
    (Witness.rising).check 42 23 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_23_2_checked :
    (Witness.rising).check 42 23 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_23_3_checked :
    (Witness.rising).check 42 23 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_23_4_checked :
    (Witness.rising).check 42 23 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_23_5_checked :
    (Witness.rising).check 42 23 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_23_6_checked :
    (Witness.rising).check 42 23 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_23_7_checked :
    (Witness.rising).check 42 23 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_23_8_checked :
    (Witness.rising).check 42 23 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_23_9 : Certificate := {
  objectiveScale := 4042263975750000
  eta := 117621422044276550400
  rows := #[⟨.count 2, 23296996636789075200⟩, ⟨.count 3, 2983152008369332800⟩, ⟨.count 4, 438698824760196000⟩, ⟨.count 5, 77294554838701200⟩, ⟨.count 6, 17010770756007600⟩, ⟨.count 7, 5543996137079400⟩, ⟨.count 8, 4017388505130000⟩, ⟨.path 9, 1437232695444000⟩, ⟨.path 10, 525147837078150⟩, ⟨.privateRow 5 13, 2054224655623140⟩, ⟨.privateRow 5 14, 3634933119441624⟩, ⟨.privateRow 5 15, 3655823539668300⟩, ⟨.privateRow 6 9, 505680807074300⟩, ⟨.privateRow 6 10, 951260206750425⟩, ⟨.privateRow 6 12, 3966692888279550⟩, ⟨.privateRow 6 13, 14921728733340⟩, ⟨.privateRow 7 5, 45913011487200⟩, ⟨.privateRow 7 6, 287999799328800⟩, ⟨.privateRow 7 7, 309912827538600⟩, ⟨.privateRow 7 8, 769042942410600⟩, ⟨.privateRow 8 2, 53086919532075⟩, ⟨.privateRow 8 3, 151424643654900⟩, ⟨.privateRow 8 4, 97086888873975⟩, ⟨.privateRow 9 0, 78886901555280⟩, ⟨.privateRow 10 0, 37565191216800⟩, ⟨.hall 4 17, 742159665947700⟩, ⟨.hall 3 19, 28828779912812880⟩]
  caps := #[0, 0, 1711836359988300, 3585484000472400, 1476834900166080, 190305277589700, 757733330080675, 0, 203217820680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_42_23_9_checked :
    (Witness.linear .positive case_42_23_9).check 42 23 9 = true := by
  change case_42_23_9.check 42 23 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_23_10 : Certificate := {
  objectiveScale := 1730729000000
  eta := 75843397021392000
  rows := #[⟨.count 2, 16076207231884800⟩, ⟨.count 3, 2402279543664000⟩, ⟨.count 4, 414679206942000⟩, ⟨.count 5, 80075984788800⟩, ⟨.count 6, 18384792426000⟩, ⟨.count 7, 5059746291600⟩, ⟨.count 8, 2053230379200⟩, ⟨.count 9, 1679915764800⟩, ⟨.path 10, 314529415200⟩, ⟨.path 11, 350523973800⟩, ⟨.privateRow 5 14, 3355565076864⟩, ⟨.privateRow 5 15, 5719713199200⟩, ⟨.privateRow 6 10, 102137735700⟩, ⟨.privateRow 6 11, 1313199459000⟩, ⟨.privateRow 6 12, 1872525154500⟩, ⟨.privateRow 6 13, 2424068927280⟩, ⟨.privateRow 6 14, 3030086159100⟩, ⟨.privateRow 7 7, 72282089880⟩, ⟨.privateRow 7 8, 436486050000⟩, ⟨.privateRow 7 9, 691393903200⟩, ⟨.privateRow 7 10, 906893301600⟩, ⟨.privateRow 7 11, 911382872400⟩, ⟨.privateRow 7 12, 333126153360⟩, ⟨.privateRow 8 4, 13749310575⟩, ⟨.privateRow 8 5, 176657808600⟩, ⟨.privateRow 8 6, 256653797400⟩, ⟨.privateRow 8 7, 387017631000⟩, ⟨.privateRow 9 2, 74868040800⟩, ⟨.privateRow 9 3, 106661318400⟩, ⟨.privateRow 10 0, 47997593280⟩, ⟨.privateRow 11 0, 26665329600⟩, ⟨.hall 5 16, 112151239200⟩, ⟨.hall 4 17, 1889846758800⟩, ⟨.hall 5 17, 4077943669800⟩, ⟨.hall 3 19, 46901648233440⟩]
  caps := #[0, 0, 20018996197200, 0, 1683633391440, 1531277603856, 0, 10353343000, 55735796025, 50813235200, 0, 3874689000, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_42_23_10_checked :
    (Witness.linear .positive case_42_23_10).check 42 23 10 = true := by
  change case_42_23_10.check 42 23 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_23_11 : Certificate := {
  objectiveScale := 233118600000
  eta := 13120259450538240
  rows := #[⟨.count 2, 2836384591360320⟩, ⟨.count 3, 514519978452480⟩, ⟨.count 4, 103463256536640⟩, ⟨.count 5, 22836484550880⟩, ⟨.count 6, 5692476469680⟩, ⟨.count 7, 1559477359440⟩, ⟨.count 8, 537750813600⟩, ⟨.count 9, 234654900480⟩, ⟨.count 10, 234654900480⟩, ⟨.path 12, 67819281530⟩, ⟨.privateRow 7 13, 172848475800⟩, ⟨.privateRow 9 9, 25529584080⟩, ⟨.privateRow 11 0, 6016792320⟩, ⟨.privateRow 12 0, 5601570975⟩, ⟨.hall 9 3, 1224847008⟩, ⟨.hall 10 3, 170931600⟩, ⟨.hall 8 5, 564671184⟩, ⟨.hall 7 7, 608469015⟩, ⟨.hall 6 10, 1065906270⟩, ⟨.hall 5 13, 7005990992⟩, ⟨.hall 4 16, 137314217040⟩]
  caps := #[0, 0, 1314928775160, 816117136120, 219947399100, 282083321520, 4343178840, 40569809280, 0, 1302540668, 0, 3080643280, 600429830, 0, 0, 0, 0, 0, 0, 0] }

theorem case_42_23_11_checked :
    (Witness.linear .positive case_42_23_11).check 42 23 11 = true := by
  change case_42_23_11.check 42 23 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_23_12 : Certificate := {
  objectiveScale := 1613898000000
  eta := 114089212613376000
  rows := #[⟨.count 2, 27096187995676800⟩, ⟨.count 3, 6263721476812800⟩, ⟨.count 4, 1614865693240800⟩, ⟨.count 5, 414785127556800⟩, ⟨.count 6, 106858768816800⟩, ⟨.count 7, 31727298002400⟩, ⟨.count 8, 10038015187200⟩, ⟨.count 9, 3519823507200⟩, ⟨.count 10, 1759911753600⟩, ⟨.count 11, 1792502712000⟩, ⟨.path 13, 322794271800⟩, ⟨.privateRow 10 4, 193590292896⟩, ⟨.privateRow 12 4, 61617280725⟩, ⟨.privateRow 13 0, 27935107200⟩, ⟨.privateRow 13 5, 12803590800⟩, ⟨.privateRow 13 9, 38410772400⟩, ⟨.privateRow 14 1, 73976302400⟩, ⟨.privateRow 15 1, 58256338140⟩, ⟨.hall 14 1, 103566823360⟩, ⟨.hall 10 3, 113954400⟩, ⟨.hall 10 5, 655237800⟩, ⟨.hall 8 7, 9895673480⟩, ⟨.hall 5 14, 896309934520⟩, ⟨.hall 4 16, 4285357876800⟩]
  caps := #[0, 0, 13307087851200, 14338192611600, 1212682957200, 2293960640400, 0, 0, 95273778600, 30766764600, 0, 0, 0, 38011373400, 0, 0, 0, 0, 0, 0] }

theorem case_42_23_12_checked :
    (Witness.linear .positive case_42_23_12).check 42 23 12 = true := by
  change case_42_23_12.check 42 23 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_23_13 : Certificate := {
  objectiveScale := 9496200000
  eta := 449442352719360
  rows := #[⟨.count 2, 117162322717440⟩, ⟨.count 3, 31183028997120⟩, ⟨.count 4, 8558385675840⟩, ⟨.count 5, 2414990017440⟩, ⟨.count 6, 726312787200⟩, ⟨.count 7, 241173092160⟩, ⟨.count 8, 86909222400⟩, ⟨.count 9, 33776084160⟩, ⟨.count 10, 17776886400⟩, ⟨.count 11, 13036383360⟩, ⟨.count 12, 9777287520⟩, ⟨.count 14, 14122748640⟩, ⟨.path 11, 1927765840⟩, ⟨.privateRow 5 15, 261976987272⟩, ⟨.privateRow 6 13, 113789003328⟩, ⟨.privateRow 6 14, 300864984420⟩, ⟨.privateRow 7 10, 399072960⟩, ⟨.privateRow 7 11, 47101694640⟩, ⟨.privateRow 7 12, 126825386688⟩, ⟨.privateRow 7 13, 205323037920⟩, ⟨.privateRow 8 8, 848722875⟩, ⟨.privateRow 8 9, 19088989920⟩, ⟨.privateRow 8 10, 54816181420⟩, ⟨.privateRow 8 11, 91797866160⟩, ⟨.privateRow 8 12, 111284543370⟩, ⟨.privateRow 9 6, 395041920⟩, ⟨.privateRow 9 7, 8542781520⟩, ⟨.privateRow 9 8, 24407947200⟩, ⟨.privateRow 9 9, 33578563200⟩, ⟨.privateRow 9 10, 74662922880⟩, ⟨.privateRow 10 5, 4108435968⟩, ⟨.privateRow 10 6, 11932734996⟩, ⟨.privateRow 10 7, 21662405856⟩, ⟨.privateRow 10 8, 8058855168⟩, ⟨.privateRow 11 3, 1896201216⟩, ⟨.privateRow 11 4, 6452351360⟩, ⟨.privateRow 11 5, 4715812920⟩, ⟨.privateRow 12 1, 1185125760⟩, ⟨.privateRow 12 2, 1846820976⟩, ⟨.privateRow 13 0, 592562880⟩, ⟨.hall 6 14, 869320452⟩, ⟨.hall 6 15, 71140379310⟩, ⟨.hall 7 15, 300651591240⟩, ⟨.hall 5 16, 173211358320⟩, ⟨.hall 4 17, 297568791520⟩, ⟨.hall 3 18, 371502619488⟩, ⟨.hall 2 20, 5167580978560⟩, ⟨.assumptionRow 13, 10590349770⟩]
  caps := #[0, 2624077032500, 0, 14112755020, 0, 4700698002, 3847543700, 488095560, 0, 416533390, 0, 0, 3075653196, 0, 0, 0, 0, 0, 0, 0] }

theorem case_42_23_13_checked :
    (Witness.linear .conditional case_42_23_13).check 42 23 13 = true := by
  change case_42_23_13.check 42 23 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_23_14 : Certificate := {
  objectiveScale := 16279200000
  eta := 398200985582400
  rows := #[⟨.count 2, 109067970211200⟩, ⟨.count 3, 30686715259200⟩, ⟨.count 4, 8988120741600⟩, ⟨.count 5, 2769067501200⟩, ⟨.count 6, 894921112800⟩, ⟨.count 7, 303794290800⟩, ⟨.count 8, 109412503200⟩, ⟨.count 9, 43807327200⟩, ⟨.count 10, 13332664800⟩, ⟨.count 11, 9311702400⟩, ⟨.count 12, 10475665200⟩, ⟨.count 13, 12969871200⟩, ⟨.path 10, 3073484700⟩, ⟨.privateRow 2 21, 13890732055200⟩, ⟨.privateRow 5 15, 591642291240⟩, ⟨.privateRow 6 13, 197574371280⟩, ⟨.privateRow 6 14, 604990450350⟩, ⟨.privateRow 7 11, 64766215800⟩, ⟨.privateRow 7 12, 228369501360⟩, ⟨.privateRow 7 13, 436984891200⟩, ⟨.privateRow 8 9, 20452489200⟩, ⟨.privateRow 8 10, 87054717750⟩, ⟨.privateRow 8 11, 184779094500⟩, ⟨.privateRow 8 12, 268293425400⟩, ⟨.privateRow 9 7, 5872721400⟩, ⟨.privateRow 9 8, 33437476800⟩, ⟨.privateRow 9 9, 80807235600⟩, ⟨.privateRow 9 10, 130321507680⟩, ⟨.privateRow 9 11, 152108775000⟩, ⟨.privateRow 10 4, 438073272⟩, ⟨.privateRow 10 5, 698377680⟩, ⟨.privateRow 10 6, 12832689870⟩, ⟨.privateRow 10 7, 36624013920⟩, ⟨.privateRow 10 8, 66028435200⟩, ⟨.privateRow 10 9, 53749685808⟩, ⟨.privateRow 11 4, 4303135200⟩, ⟨.privateRow 11 5, 16851006900⟩, ⟨.privateRow 11 6, 36400291200⟩, ⟨.privateRow 12 2, 756575820⟩, ⟨.privateRow 12 3, 8147739600⟩, ⟨.privateRow 12 4, 9093459375⟩, ⟨.privateRow 13 1, 3442004280⟩, ⟨.privateRow 13 2, 1163962800⟩, ⟨.privateRow 14 0, 972740340⟩, ⟨.hall 7 12, 708450435⟩, ⟨.hall 7 13, 9542416455⟩, ⟨.hall 6 14, 7778743830⟩, ⟨.hall 8 14, 164972327520⟩, ⟨.hall 6 15, 160430631075⟩, ⟨.hall 5 16, 420023203600⟩, ⟨.hall 4 17, 688218531000⟩, ⟨.hall 3 18, 945162298080⟩, ⟨.hall 2 20, 17835013996800⟩, ⟨.assumptionRow 14, 10130749650⟩]
  caps := #[0, 1704338634600, 255394194300, 0, 13163361120, 0, 12488897850, 1452573540, 0, 2227480710, 0, 819047250, 3011753745, 0, 0, 16279200000, 0, 0, 0, 0] }

theorem case_42_23_14_checked :
    (Witness.linear .conditional case_42_23_14).check 42 23 14 = true := by
  change case_42_23_14.check 42 23 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_24_1_checked :
    (Witness.rising).check 42 24 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_24_2_checked :
    (Witness.rising).check 42 24 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_24_3_checked :
    (Witness.rising).check 42 24 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_24_4_checked :
    (Witness.rising).check 42 24 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_24_5_checked :
    (Witness.rising).check 42 24 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_24_6_checked :
    (Witness.rising).check 42 24 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_24_7_checked :
    (Witness.rising).check 42 24 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_24_8_checked :
    (Witness.rising).check 42 24 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_24_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_42_24_9_checked :
    (Witness.linear .positive case_42_24_9).check 42 24 9 = true := by
  change case_42_24_9.check 42 24 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_24_10 : Certificate := {
  objectiveScale := 200200000
  eta := 10922626915200
  rows := #[⟨.count 2, 1899587289600⟩, ⟨.count 3, 289826737200⟩, ⟨.count 4, 50748778080⟩, ⟨.count 5, 9644263200⟩, ⟨.count 6, 2225599200⟩, ⟨.count 7, 581981400⟩, ⟨.count 8, 227908800⟩, ⟨.count 9, 205117920⟩, ⟨.path 10, 40035996⟩, ⟨.path 11, 38132094⟩, ⟨.privateRow 4 18, 2909907000⟩, ⟨.privateRow 5 15, 1609594272⟩, ⟨.privateRow 5 16, 490527180⟩, ⟨.privateRow 6 13, 1308925200⟩, ⟨.privateRow 6 15, 332560800⟩, ⟨.privateRow 7 12, 616090200⟩, ⟨.privateRow 8 9, 9665775⟩, ⟨.privateRow 8 12, 167675760⟩, ⟨.privateRow 8 13, 83430900⟩, ⟨.privateRow 9 9, 8372160⟩, ⟨.privateRow 9 11, 8465184⟩, ⟨.privateRow 10 3, 5969040⟩, ⟨.privateRow 11 0, 2616300⟩, ⟨.hall 8 3, 366282⟩, ⟨.hall 4 15, 846846⟩, ⟨.hall 3 18, 39819780⟩]
  caps := #[0, 0, 0, 0, 3947944, 44147532, 0, 52547000, 16227940, 0, 4147472, 1503894, 0, 0, 0, 0, 0, 0, 0] }

theorem case_42_24_10_checked :
    (Witness.linear .positive case_42_24_10).check 42 24 10 = true := by
  change case_42_24_10.check 42 24 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_24_11 : Certificate := {
  objectiveScale := 53678625000
  eta := 4634874262418400
  rows := #[⟨.count 2, 890156846779200⟩, ⟨.count 3, 182633620068900⟩, ⟨.count 4, 38449183172400⟩, ⟨.count 5, 8322334020000⟩, ⟨.count 6, 1920538620000⟩, ⟨.count 7, 515344529700⟩, ⟨.count 8, 146659312800⟩, ⟨.count 9, 58663725120⟩, ⟨.count 10, 48886437600⟩, ⟨.path 11, 9634239615⟩, ⟨.path 12, 8258250000⟩, ⟨.privateRow 3 21, 18350746514100⟩, ⟨.privateRow 5 16, 2055616502940⟩, ⟨.privateRow 6 14, 1083183781680⟩, ⟨.privateRow 6 17, 4106751749100⟩, ⟨.privateRow 7 13, 1019165827680⟩, ⟨.privateRow 7 15, 13870556700⟩, ⟨.privateRow 8 12, 183324141000⟩, ⟨.privateRow 11 0, 2327925600⟩, ⟨.privateRow 12 0, 246222900⟩, ⟨.privateRow 12 1, 5601570975⟩, ⟨.privateRow 12 8, 8322334020⟩, ⟨.privateRow 12 10, 4267863600⟩, ⟨.privateRow 13 4, 8002244250⟩, ⟨.privateRow 13 10, 3200897700⟩, ⟨.hall 12 2, 2230928700⟩, ⟨.hall 9 3, 279351072⟩, ⟨.hall 10 3, 184667175⟩, ⟨.hall 10 7, 9496200⟩, ⟨.hall 6 11, 387611400⟩, ⟨.hall 8 11, 430517010⟩, ⟨.hall 9 11, 75209904⟩, ⟨.hall 5 13, 592509775⟩, ⟨.hall 4 16, 16040032008⟩, ⟨.hall 3 19, 1177610263830⟩]
  caps := #[0, 6875634956190, 0, 117899731950, 0, 34658884260, 0, 0, 12729717000, 5848048206, 4792187400, 4204652760, 19022294445, 0, 0, 0, 0, 0, 0] }

theorem case_42_24_11_checked :
    (Witness.linear .positive case_42_24_11).check 42 24 11 = true := by
  change case_42_24_11.check 42 24 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_24_12 : Certificate := {
  objectiveScale := 46475000
  eta := 4578796862640
  rows := #[⟨.count 2, 1125784820160⟩, ⟨.count 3, 275771886390⟩, ⟨.count 4, 66578672160⟩, ⟨.count 5, 17725490640⟩, ⟨.count 6, 4788875520⟩, ⟨.count 7, 1309458150⟩, ⟨.count 8, 380933280⟩, ⟨.count 9, 133326648⟩, ⟨.count 10, 63488880⟩, ⟨.count 11, 58198140⟩, ⟨.path 12, 10328175⟩, ⟨.hall 6 12, 2492325⟩]
  caps := #[0, 0, 1813380140, 422532110, 0, 0, 0, 0, 6364345, 936052, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_42_24_12_checked :
    (Witness.linear .positive case_42_24_12).check 42 24 12 = true := by
  change case_42_24_12.check 42 24 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_24_13 : Certificate := {
  objectiveScale := 4526156250
  eta := 520645216291200
  rows := #[⟨.count 2, 122504756774400⟩, ⟨.count 3, 28087877317500⟩, ⟨.count 4, 7356943273680⟩, ⟨.count 5, 1949803970400⟩, ⟨.count 6, 532263560400⟩, ⟨.count 7, 156843987300⟩, ⟨.count 8, 51214363200⟩, ⟨.count 9, 18856197360⟩, ⟨.count 10, 6983776800⟩, ⟨.count 11, 6401795400⟩, ⟨.count 12, 5487253200⟩, ⟨.path 10, 1777836060⟩, ⟨.privateRow 2 22, 332893360800⟩, ⟨.privateRow 4 18, 968164857660⟩, ⟨.privateRow 5 15, 80845530480⟩, ⟨.privateRow 5 16, 363210434730⟩, ⟨.privateRow 5 17, 802114478880⟩, ⟨.privateRow 6 13, 57768582300⟩, ⟨.privateRow 6 14, 152911455840⟩, ⟨.privateRow 6 15, 317117507850⟩, ⟨.privateRow 6 16, 434102697600⟩, ⟨.privateRow 7 11, 30179892600⟩, ⟨.privateRow 7 12, 68895512400⟩, ⟨.privateRow 7 13, 134163340740⟩, ⟨.privateRow 7 14, 182794122225⟩, ⟨.privateRow 7 15, 182146321500⟩, ⟨.privateRow 8 8, 323323000⟩, ⟨.privateRow 8 9, 13894805925⟩, ⟨.privateRow 8 10, 32299967700⟩, ⟨.privateRow 8 11, 44279084850⟩, ⟨.privateRow 8 12, 118491413040⟩, ⟨.privateRow 8 13, 43648605000⟩, ⟨.privateRow 9 6, 442305864⟩, ⟨.privateRow 9 7, 6259533280⟩, ⟨.privateRow 9 8, 14083949880⟩, ⟨.privateRow 9 9, 33655152960⟩, ⟨.privateRow 9 10, 31155404280⟩, ⟨.privateRow 10 4, 232792560⟩, ⟨.privateRow 10 5, 3165978816⟩, ⟨.privateRow 10 6, 7785617840⟩, ⟨.privateRow 10 7, 15277011750⟩, ⟨.privateRow 11 3, 1798851600⟩, ⟨.privateRow 11 4, 4481256780⟩, ⟨.privateRow 11 5, 937636700⟩, ⟨.privateRow 12 1, 914542200⟩, ⟨.privateRow 12 2, 789831900⟩, ⟨.privateRow 13 0, 457271100⟩, ⟨.privateRow 14 0, 432329040⟩, ⟨.hall 6 17, 175896949800⟩, ⟨.hall 5 18, 1003060258200⟩, ⟨.hall 4 19, 2593239280632⟩, ⟨.hall 3 20, 4957733266200⟩, ⟨.hall 2 21, 5871028363200⟩, ⟨.assumptionRow 13, 5253858720⟩]
  caps := #[0, 0, 0, 22762474020, 0, 3353321400, 1905720960, 0, 107124930, 438481472, 1042485444, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_42_24_13_checked :
    (Witness.linear .conditional case_42_24_13).check 42 24 13 = true := by
  change case_42_24_13.check 42 24 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_24_14 : Certificate := {
  objectiveScale := 67400676000000
  eta := 7531904760988608000
  rows := #[⟨.count 2, 1751764274727667200⟩, ⟨.count 3, 402582013525692000⟩, ⟨.count 4, 102924671394504960⟩, ⟨.count 5, 26656224024830400⟩, ⟨.count 6, 7078365072979200⟩, ⟨.count 7, 1933442311600800⟩, ⟨.count 8, 571989096806400⟩, ⟨.count 9, 171596729041920⟩, ⟨.count 10, 71498637100800⟩, ⟨.count 11, 65540417342400⟩, ⟨.path 9, 37519687296000⟩, ⟨.privateRow 2 22, 40897220421657600⟩, ⟨.privateRow 4 18, 15904474608422400⟩, ⟨.privateRow 5 15, 842287992017472⟩, ⟨.privateRow 5 16, 5665969079250480⟩, ⟨.privateRow 5 17, 13924529810231040⟩, ⟨.privateRow 6 13, 546170144520000⟩, ⟨.privateRow 6 14, 2194667689294080⟩, ⟨.privateRow 6 15, 5364951305313600⟩, ⟨.privateRow 6 16, 8442229948152000⟩, ⟨.privateRow 7 11, 247448514456000⟩, ⟨.privateRow 7 12, 888696849440400⟩, ⟨.privateRow 7 13, 2171260397386080⟩, ⟨.privateRow 7 14, 3545034359466600⟩, ⟨.privateRow 7 15, 4299139280436000⟩, ⟨.privateRow 8 9, 93841961194800⟩, ⟨.privateRow 8 10, 366430515141600⟩, ⟨.privateRow 8 11, 930971837250000⟩, ⟨.privateRow 8 12, 1586673921661920⟩, ⟨.privateRow 8 13, 2031752937614400⟩, ⟨.privateRow 8 14, 1556088393568800⟩, ⟨.privateRow 9 7, 29658693908480⟩, ⟨.privateRow 9 8, 150742959887520⟩, ⟨.privateRow 9 9, 421161019493760⟩, ⟨.privateRow 9 10, 769801992785280⟩, ⟨.privateRow 9 11, 1047693362317056⟩, ⟨.privateRow 10 5, 5243233387392⟩, ⟨.privateRow 10 6, 60376626885120⟩, ⟨.privateRow 10 7, 143295185189520⟩, ⟨.privateRow 10 8, 517854414430080⟩, ⟨.privateRow 10 9, 155310928368960⟩, ⟨.privateRow 11 4, 18768392238960⟩, ⟨.privateRow 11 5, 97317589387200⟩, ⟨.privateRow 11 6, 174650316668100⟩, ⟨.privateRow 12 1, 2340729190800⟩, ⟨.privateRow 12 3, 43537562948880⟩, ⟨.privateRow 12 4, 40052477264800⟩, ⟨.privateRow 13 1, 15321136521600⟩, ⟨.privateRow 13 2, 4681458381600⟩, ⟨.privateRow 14 0, 4426106106240⟩, ⟨.hall 6 17, 7590204522700800⟩, ⟨.hall 5 18, 24055304305032000⟩, ⟨.hall 4 19, 52604049767357088⟩, ⟨.hall 3 20, 93053348251063200⟩, ⟨.hall 2 21, 113706665869305600⟩, ⟨.assumptionRow 14, 50281325550225⟩]
  caps := #[0, 0, 5547431203949250, 401774113295100, 7856018933490, 241198869703428, 0, 12064188633120, 24701316243240, 0, 9665975878944, 1126012543425, 22192575260625, 146771350982550, 0, 67400676000000, 0, 0, 0] }

theorem case_42_24_14_checked :
    (Witness.linear .conditional case_42_24_14).check 42 24 14 = true := by
  change case_42_24_14.check 42 24 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_24_15 : Certificate := {
  objectiveScale := 18117099000000
  eta := 1825038461316470400
  rows := #[⟨.count 2, 414084356769283200⟩, ⟨.count 3, 103521089192320800⟩, ⟨.count 4, 25901572933716480⟩, ⟨.count 5, 6481479129325200⟩, ⟨.count 6, 1601058766507200⟩, ⟨.count 7, 393242504054400⟩, ⟨.count 8, 89373296376000⟩, ⟨.count 9, 16087193347680⟩, ⟨.path 9, 12107236050000⟩, ⟨.privateRow 2 22, 35785067868950400⟩, ⟨.privateRow 4 17, 740197088360730⟩, ⟨.privateRow 4 18, 5424561875372640⟩, ⟨.privateRow 5 15, 464962446460512⟩, ⟨.privateRow 5 16, 1926186051109320⟩, ⟨.privateRow 5 17, 4742941535011680⟩, ⟨.privateRow 6 13, 205203925726800⟩, ⟨.privateRow 6 14, 710177236488720⟩, ⟨.privateRow 6 15, 1781294914198800⟩, ⟨.privateRow 6 16, 2989891419715200⟩, ⟨.privateRow 7 11, 77076868354200⟩, ⟨.privateRow 7 12, 265867823921700⟩, ⟨.privateRow 7 13, 691685475881400⟩, ⟨.privateRow 7 14, 1228297642872300⟩, ⟨.privateRow 7 15, 1661137482404400⟩, ⟨.privateRow 8 9, 25508628340650⟩, ⟨.privateRow 8 10, 98949006702000⟩, ⟨.privateRow 8 11, 278050255392000⟩, ⟨.privateRow 8 12, 530728424979480⟩, ⟨.privateRow 8 13, 770099903773200⟩, ⟨.privateRow 8 14, 819006957623400⟩, ⟨.privateRow 9 7, 7017458826560⟩, ⟨.privateRow 9 8, 35525885309460⟩, ⟨.privateRow 9 9, 114823406486880⟩, ⟨.privateRow 9 10, 242896758817440⟩, ⟨.privateRow 9 11, 384781831997472⟩, ⟨.privateRow 9 12, 350194366299960⟩, ⟨.privateRow 10 5, 1132061754096⟩, ⟨.privateRow 10 6, 11519224866240⟩, ⟨.privateRow 10 7, 47591280320220⟩, ⟨.privateRow 10 8, 77541974284320⟩, ⟨.privateRow 10 9, 288377836306560⟩, ⟨.privateRow 10 10, 19185467622048⟩, ⟨.privateRow 11 4, 2159854662420⟩, ⟨.privateRow 11 5, 18784942849400⟩, ⟨.privateRow 11 6, 58930517297925⟩, ⟨.privateRow 11 7, 87458154310800⟩, ⟨.privateRow 12 3, 4681458381600⟩, ⟨.privateRow 12 4, 29389155395600⟩, ⟨.privateRow 12 5, 24870247652250⟩, ⟨.privateRow 13 2, 10065135520440⟩, ⟨.privateRow 13 3, 8322592678400⟩, ⟨.privateRow 14 1, 4868716716864⟩, ⟨.hall 7 16, 538298868907800⟩, ⟨.hall 6 17, 3703033579845600⟩, ⟨.hall 5 18, 9663762062354400⟩, ⟨.hall 4 19, 19681787327922720⟩, ⟨.hall 3 20, 34461385511553000⟩, ⟨.hall 2 21, 47945794395844800⟩, ⟨.assumptionRow 15, 3683446943400⟩]
  caps := #[0, 1640579422204800, 917933207360400, 121320856238400, 3382927722720, 0, 5580827046600, 7070499586800, 3558030422310, 0, 3609723273156, 10612566541850, 3683446943400, 12686837689680, 3683446943400, 141253345056600, 18117099000000, 0, 0] }

theorem case_42_24_15_checked :
    (Witness.linear .conditional case_42_24_15).check 42 24 15 = true := by
  change case_42_24_15.check 42 24 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_25_1_checked :
    (Witness.rising).check 42 25 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_25_2_checked :
    (Witness.rising).check 42 25 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_25_3_checked :
    (Witness.rising).check 42 25 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_25_4_checked :
    (Witness.rising).check 42 25 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_25_5_checked :
    (Witness.rising).check 42 25 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_25_6_checked :
    (Witness.rising).check 42 25 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_25_7_checked :
    (Witness.rising).check 42 25 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_25_8_checked :
    (Witness.rising).check 42 25 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_25_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_42_25_9_checked :
    (Witness.linear .positive case_42_25_9).check 42 25 9 = true := by
  change case_42_25_9.check 42 25 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_25_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_42_25_10_checked :
    (Witness.linear .positive case_42_25_10).check 42 25 10 = true := by
  change case_42_25_10.check 42 25 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_25_11 : Certificate := {
  objectiveScale := 975975000
  eta := 127952102678400
  rows := #[⟨.count 2, 26480153700000⟩, ⟨.count 3, 5444319600720⟩, ⟨.count 4, 1113679607040⟩, ⟨.count 5, 251415964800⟩, ⟨.count 6, 57034177200⟩, ⟨.count 7, 13332664800⟩, ⟨.count 8, 4147940160⟩, ⟨.count 9, 1185125760⟩, ⟨.count 10, 740703600⟩, ⟨.path 11, 390390000⟩, ⟨.privateRow 6 19, 651431180400⟩, ⟨.privateRow 7 17, 27353125800⟩, ⟨.privateRow 8 11, 7079010120⟩, ⟨.privateRow 12 13, 193993800⟩, ⟨.privateRow 13 1, 38798760⟩, ⟨.hall 11 2, 4263600⟩, ⟨.hall 12 3, 1627920⟩, ⟨.hall 13 3, 6877962⟩, ⟨.hall 10 4, 387600⟩, ⟨.hall 7 9, 1824760⟩, ⟨.hall 6 11, 298375⟩, ⟨.hall 3 19, 5681196612⟩]
  caps := #[0, 0, 0, 0, 2835792960, 0, 353152800, 330985200, 0, 181239240, 235271400, 0, 547872600, 0, 0, 0, 0, 0] }

theorem case_42_25_11_checked :
    (Witness.linear .positive case_42_25_11).check 42 25 11 = true := by
  change case_42_25_11.check 42 25 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_25_12 : Certificate := {
  objectiveScale := 7150000
  eta := 1240784344800
  rows := #[⟨.count 2, 279933053400⟩, ⟨.count 3, 69604975440⟩, ⟨.count 4, 17004942240⟩, ⟨.count 5, 4101583200⟩, ⟨.count 6, 1094679300⟩, ⟨.count 7, 299808600⟩, ⟨.count 8, 84651840⟩, ⟨.count 9, 28217280⟩, ⟨.count 10, 8817900⟩, ⟨.count 11, 13856700⟩, ⟨.path 11, 2383238⟩, ⟨.hall 9 11, 389538⟩, ⟨.hall 10 11, 1086895⟩, ⟨.hall 8 12, 343140⟩]
  caps := #[0, 0, 264201080, 0, 34800480, 0, 6376656, 479388, 0, 382148, 3098576, 0, 0, 0, 0, 0, 0, 0] }

theorem case_42_25_12_checked :
    (Witness.linear .positive case_42_25_12).check 42 25 12 = true := by
  change case_42_25_12.check 42 25 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_25_13 : Certificate := {
  objectiveScale := 58443000000
  eta := 11898274501713600
  rows := #[⟨.count 2, 2505605103401400⟩, ⟨.count 3, 586874350422360⟩, ⟨.count 4, 133989577722000⟩, ⟨.count 5, 35043428019600⟩, ⟨.count 6, 9276201534600⟩, ⟨.count 7, 2529873145800⟩, ⟨.count 8, 749592043200⟩, ⟨.count 9, 224877612960⟩, ⟨.count 10, 93699005400⟩, ⟨.path 9, 11457165720⟩, ⟨.path 10, 22632135240⟩, ⟨.privateRow 2 23, 73694267747100⟩, ⟨.privateRow 3 21, 61635205752120⟩, ⟨.privateRow 4 18, 8422202028240⟩, ⟨.privateRow 4 19, 25075192402260⟩, ⟨.privateRow 5 16, 5842534553856⟩, ⟨.privateRow 5 17, 10321614723420⟩, ⟨.privateRow 5 18, 18572035241760⟩, ⟨.privateRow 6 13, 469769843400⟩, ⟨.privateRow 6 14, 2462201641900⟩, ⟨.privateRow 6 15, 4638100767300⟩, ⟨.privateRow 6 16, 7595196759150⟩, ⟨.privateRow 6 17, 8719956645400⟩, ⟨.privateRow 7 11, 389854790325⟩, ⟨.privateRow 7 12, 1095704695800⟩, ⟨.privateRow 7 13, 2001143043900⟩, ⟨.privateRow 7 14, 2047992546600⟩, ⟨.privateRow 7 15, 6575662343250⟩, ⟨.privateRow 8 9, 232165313380⟩, ⟨.privateRow 8 10, 548139181590⟩, ⟨.privateRow 8 11, 459125126460⟩, ⟨.privateRow 8 12, 2539243046340⟩, ⟨.privateRow 8 13, 490982788296⟩, ⟨.privateRow 9 6, 1514327360⟩, ⟨.privateRow 9 7, 121600487008⟩, ⟨.privateRow 9 8, 299836817280⟩, ⟨.privateRow 9 9, 497645828680⟩, ⟨.privateRow 9 10, 468792484160⟩, ⟨.privateRow 10 4, 1561650090⟩, ⟨.privateRow 10 5, 63885685500⟩, ⟨.privateRow 10 6, 174280150044⟩, ⟨.privateRow 10 7, 167617109660⟩, ⟨.privateRow 11 3, 36810323550⟩, ⟨.privateRow 11 4, 68144731200⟩, ⟨.privateRow 12 1, 22652506800⟩, ⟨.privateRow 13 0, 4530501360⟩, ⟨.hall 5 19, 10571924923560⟩, ⟨.hall 4 20, 42038090643120⟩, ⟨.hall 3 21, 100492183291500⟩, ⟨.hall 2 22, 82141436777400⟩, ⟨.assumptionRow 13, 72401993664⟩]
  caps := #[0, 81525444299112, 4183475742732, 1788612859176, 1320263604660, 129852798504, 138804134326, 33727037344, 63606069670, 36080362752, 48299896086, 91956381972, 27096980064, 0, 58443000000, 0, 0, 0] }

theorem case_42_25_13_checked :
    (Witness.linear .conditional case_42_25_13).check 42 25 13 = true := by
  change case_42_25_13.check 42 25 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_25_14 : Certificate := {
  objectiveScale := 576975297822000000
  eta := 163844781268764205209600
  rows := #[⟨.count 2, 32099398253375679626400⟩, ⟨.count 3, 6892508827411955748000⟩, ⟨.count 4, 1423514068028754942240⟩, ⟨.count 5, 322443898048471399200⟩, ⟨.count 6, 72495775735730146800⟩, ⟨.count 7, 16525495690098595200⟩, ⟨.count 8, 4406798850692958720⟩, ⟨.count 9, 1101699712673239680⟩, ⟨.count 10, 688562320420774800⟩, ⟨.count 11, 1082026503518360400⟩, ⟨.path 8, 1028747616008112000⟩, ⟨.privateRow 2 23, 1033876324111793362200⟩, ⟨.privateRow 3 20, 13128588242689439520⟩, ⟨.privateRow 3 21, 777868853379349291560⟩, ⟨.privateRow 4 18, 101277680729318533440⟩, ⟨.privateRow 4 19, 308521823703201828720⟩, ⟨.privateRow 5 16, 62930661444627840864⟩, ⟨.privateRow 5 17, 122377197547926561240⟩, ⟨.privateRow 5 18, 240065613580606894080⟩, ⟨.privateRow 6 13, 3632517547525924200⟩, ⟨.privateRow 6 14, 24766384413864693600⟩, ⟨.privateRow 6 15, 52334015220171364680⟩, ⟨.privateRow 6 16, 96751203189600059100⟩, ⟨.privateRow 6 17, 127318451913993740400⟩, ⟨.privateRow 7 11, 2520629922968907750⟩, ⟨.privateRow 7 12, 10075493545748888400⟩, ⟨.privateRow 7 13, 21591347047480009800⟩, ⟨.privateRow 7 14, 42435112147074606960⟩, ⟨.privateRow 7 15, 56314561205841939000⟩, ⟨.privateRow 7 16, 55871913999857155200⟩, ⟨.privateRow 8 9, 1155254559817077720⟩, ⟨.privateRow 8 10, 4441226966713997460⟩, ⟨.privateRow 8 11, 9482486812651812960⟩, ⟨.privateRow 8 12, 19302697049129053560⟩, ⟨.privateRow 8 13, 27873002730632963904⟩, ⟨.privateRow 8 14, 13306466842131473010⟩, ⟨.privateRow 9 7, 403956561313521216⟩, ⟨.privateRow 9 8, 2033384037588263360⟩, ⟨.privateRow 9 9, 4605716854370071440⟩, ⟨.privateRow 9 10, 9618013364607648000⟩, ⟨.privateRow 9 11, 11006796203466903840⟩, ⟨.privateRow 10 5, 87635204417189520⟩, ⟨.privateRow 10 6, 915787886159630484⟩, ⟨.privateRow 10 7, 2440570891269190680⟩, ⟨.privateRow 10 8, 5448249360329380605⟩, ⟨.privateRow 10 9, 560686460914059480⟩, ⟨.privateRow 11 4, 357694711906896000⟩, ⟨.privateRow 11 5, 1357451431686670320⟩, ⟨.privateRow 11 6, 1300617716350352400⟩, ⟨.privateRow 12 0, 12881267899028100⟩, ⟨.privateRow 12 2, 60112583528797800⟩, ⟨.privateRow 12 3, 704956661383174200⟩, ⟨.privateRow 12 4, 36067550117278680⟩, ⟨.privateRow 13 1, 180337750586393400⟩, ⟨.hall 6 18, 11105008851898962000⟩, ⟨.hall 5 19, 212293599990302310480⟩, ⟨.hall 4 20, 629368444532193743520⟩, ⟨.hall 3 21, 1357913752101809983080⟩, ⟨.hall 2 22, 1100232775555821507600⟩, ⟨.assumptionRow 14, 480499822234000800⟩]
  caps := #[0, 83470729021122643200, 0, 33293889666049172160, 0, 0, 96398142994459020, 1384717474114577460, 0, 243324278440763520, 743472265434000921, 0, 350186877324578580, 480499822234000800, 5289253155985999200, 576975297822000000, 0, 0] }

theorem case_42_25_14_checked :
    (Witness.linear .conditional case_42_25_14).check 42 25 14 = true := by
  change case_42_25_14.check 42 25 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_25_15 : Certificate := {
  objectiveScale := 319040690997600000
  eta := 84022964753212412928000
  rows := #[⟨.count 2, 17001521774282824178400⟩, ⟨.count 3, 3623490354982285307520⟩, ⟨.count 4, 735200941590608613120⟩, ⟨.count 5, 159418571518371765600⟩, ⟨.count 6, 32821470606723598800⟩, ⟨.count 7, 6197060883786973200⟩, ⟨.count 8, 1101699712673239680⟩, ⟨.count 9, 183616618778873280⟩, ⟨.path 8, 602935559295189120⟩, ⟨.privateRow 2 23, 1099519265325240559800⟩, ⟨.privateRow 3 20, 59808013105585224480⟩, ⟨.privateRow 3 21, 507638745383991661440⟩, ⟨.privateRow 4 18, 69042307812000713190⟩, ⟨.privateRow 4 19, 198022872660565712760⟩, ⟨.privateRow 5 16, 35923279916809565280⟩, ⟨.privateRow 5 17, 75633652595933391960⟩, ⟨.privateRow 5 18, 158697220516026192000⟩, ⟨.privateRow 6 13, 1580102195614113600⟩, ⟨.privateRow 6 14, 13114561973199386700⟩, ⟨.privateRow 6 15, 30465057332394725040⟩, ⟨.privateRow 6 16, 62472002432303113650⟩, ⟨.privateRow 6 17, 91671689881416645000⟩, ⟨.privateRow 7 11, 1012350554428162950⟩, ⟨.privateRow 7 12, 4866777217123707600⟩, ⟨.privateRow 7 13, 11842178955173166600⟩, ⟨.privateRow 7 14, 26230945539839040000⟩, ⟨.privateRow 7 15, 39944811754886138100⟩, ⟨.privateRow 7 16, 46745730864121489200⟩, ⟨.privateRow 8 9, 408036930619718400⟩, ⟨.privateRow 8 10, 1902153410162390385⟩, ⟨.privateRow 8 11, 4783868692828144920⟩, ⟨.privateRow 8 12, 11315374132248065880⟩, ⟨.privateRow 8 13, 14877536536558207512⟩, ⟨.privateRow 8 14, 32098480170281785260⟩, ⟨.privateRow 9 7, 110169971267323968⟩, ⟨.privateRow 9 8, 741267090625821760⟩, ⟨.privateRow 9 9, 2068237192078697640⟩, ⟨.privateRow 9 10, 5208299964410262720⟩, ⟨.privateRow 9 11, 9612670023849532640⟩, ⟨.privateRow 9 12, 8593257758851269504⟩, ⟨.privateRow 10 5, 6259657458370680⟩, ⟨.privateRow 10 6, 257063266290422592⟩, ⟨.privateRow 10 7, 930834247976232600⟩, ⟨.privateRow 10 8, 2625143846604203925⟩, ⟨.privateRow 10 9, 5334718549164764760⟩, ⟨.privateRow 10 10, 910432401445246680⟩, ⟨.privateRow 11 4, 35769471190689600⟩, ⟨.privateRow 11 5, 396743051290065480⟩, ⟨.privateRow 11 6, 1424486070288481200⟩, ⟨.privateRow 11 7, 1819771846826333400⟩, ⟨.privateRow 12 0, 4293755966342700⟩, ⟨.privateRow 12 3, 71042144170397400⟩, ⟨.privateRow 12 4, 763429810815732060⟩, ⟨.privateRow 12 5, 394071380911007800⟩, ⟨.privateRow 13 2, 196732091548792800⟩, ⟨.privateRow 13 3, 173124240562937664⟩, ⟨.privateRow 14 1, 85250573004476880⟩, ⟨.hall 6 18, 39959048945721906000⟩, ⟨.hall 5 19, 188380814262546545640⟩, ⟨.hall 4 20, 469414012269222408960⟩, ⟨.hall 3 21, 938992436357810594760⟩, ⟨.hall 2 22, 773445089949747415200⟩, ⟨.assumptionRow 15, 123991991501947800⟩]
  caps := #[0, 34169460577457636640, 9655309201101022800, 5658867086198245920, 577950119699032080, 817948183508158560, 0, 26103581749905660, 0, 0, 139036215985927533, 188774108625267000, 0, 123991991501947800, 777539695243681920, 2747374227476452200, 319040690997600000, 0] }

theorem case_42_25_15_checked :
    (Witness.linear .conditional case_42_25_15).check 42 25 15 = true := by
  change case_42_25_15.check 42 25 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_25_16 : Certificate := {
  objectiveScale := 40286030400000
  eta := 9544065969870432000
  rows := #[⟨.count 2, 2039659259690052000⟩, ⟨.count 3, 429482968644169440⟩, ⟨.count 4, 89723016490947840⟩, ⟨.count 5, 19115197706404800⟩, ⟨.count 6, 4313606562064800⟩, ⟨.count 7, 968831420356800⟩, ⟨.count 8, 215295871190400⟩, ⟨.count 9, 43059174238080⟩, ⟨.path 6, 190571095915200⟩, ⟨.path 9, 22384993831200⟩, ⟨.path 10, 2504496182760⟩, ⟨.privateRow 7 11, 11533707385200⟩, ⟨.privateRow 7 12, 367980188004000⟩, ⟨.privateRow 8 9, 5382396779760⟩, ⟨.privateRow 8 10, 144651913456050⟩, ⟨.privateRow 8 14, 3653301814262100⟩, ⟨.privateRow 9 7, 1435305807936⟩, ⟨.privateRow 9 8, 45185553212800⟩, ⟨.privateRow 9 11, 1342010930420160⟩, ⟨.privateRow 9 12, 15309928617984⟩, ⟨.privateRow 9 14, 5715706684047360⟩, ⟨.privateRow 10 6, 10226553881544⟩, ⟨.privateRow 10 7, 55618100057520⟩, ⟨.privateRow 10 8, 38349577055790⟩, ⟨.privateRow 10 9, 56899623100320⟩, ⟨.privateRow 11 4, 1398025137600⟩, ⟨.privateRow 11 10, 1543978961965440⟩, ⟨.privateRow 12 3, 1281523042800⟩, ⟨.privateRow 12 4, 2819350694160⟩, ⟨.hall 12 3, 2957360868000⟩, ⟨.hall 13 3, 999587973384⟩, ⟨.hall 11 4, 1239275030400⟩, ⟨.hall 13 5, 832989977820⟩, ⟨.hall 14 5, 2221306607520⟩, ⟨.hall 9 7, 1555907880303⟩, ⟨.hall 11 7, 1051506086400⟩, ⟨.hall 12 7, 630903651840⟩, ⟨.hall 8 9, 351151019856⟩, ⟨.hall 7 11, 2022071332050⟩, ⟨.hall 6 14, 18711294441840⟩, ⟨.hall 5 15, 20119515015600⟩]
  caps := #[0, 14383582747974000, 0, 0, 218775201099840, 35615654886240, 0, 74729173764960, 0, 20343155449760, 6387987110076, 41523077887200, 690050869200, 0, 128473579268496, 168110552887200, 322288243200000, 40286030400000] }

theorem case_42_25_16_checked :
    (Witness.linear .negative case_42_25_16).check 42 25 16 = true := by
  change case_42_25_16.check 42 25 16 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_26_1_checked :
    (Witness.rising).check 42 26 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_26_2_checked :
    (Witness.rising).check 42 26 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_26_3_checked :
    (Witness.rising).check 42 26 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_26_4_checked :
    (Witness.rising).check 42 26 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_26_5_checked :
    (Witness.rising).check 42 26 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_26_6_checked :
    (Witness.rising).check 42 26 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_26_7_checked :
    (Witness.rising).check 42 26 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_26_8_checked :
    (Witness.rising).check 42 26 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_26_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_42_26_9_checked :
    (Witness.linear .positive case_42_26_9).check 42 26 9 = true := by
  change case_42_26_9.check 42 26 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_26_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_42_26_10_checked :
    (Witness.linear .positive case_42_26_10).check 42 26 10 = true := by
  change case_42_26_10.check 42 26 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_26_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_42_26_11_checked :
    (Witness.linear .positive case_42_26_11).check 42 26 11 = true := by
  change case_42_26_11.check 42 26 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_26_12 : Certificate := {
  objectiveScale := 460000
  eta := 224877612960
  rows := #[⟨.count 2, 47474162736⟩, ⟨.count 3, 9659921271⟩, ⟨.count 4, 2141691552⟩, ⟨.count 5, 457626400⟩, ⟨.count 6, 106086120⟩, ⟨.count 7, 24025386⟩, ⟨.count 8, 5824336⟩, ⟨.count 9, 1092063⟩, ⟨.path 9, 640679⟩]
  caps := #[0, 274731849, 0, 0, 0, 459085, 0, 353626, 319738, 468616, 460000, 460000, 0, 0, 0, 0, 0] }

theorem case_42_26_12_checked :
    (Witness.linear .positive case_42_26_12).check 42 26 12 = true := by
  change case_42_26_12.check 42 26 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_26_13 : Certificate := {
  objectiveScale := 24420825000
  eta := 10973746415431800
  rows := #[⟨.count 2, 2130434285779800⟩, ⟨.count 3, 430680785535000⟩, ⟨.count 4, 94882289982480⟩, ⟨.count 5, 21423608306100⟩, ⟨.count 6, 5180216441400⟩, ⟨.count 7, 1264936572900⟩, ⟨.count 8, 374796021600⟩, ⟨.count 9, 84329104860⟩, ⟨.path 9, 30683984760⟩, ⟨.privateRow 2 24, 68334684638220⟩, ⟨.privateRow 3 21, 12633303042360⟩, ⟨.privateRow 3 22, 51394573740510⟩, ⟨.privateRow 4 18, 636082390944⟩, ⟨.privateRow 4 19, 13351104351585⟩, ⟨.privateRow 4 20, 20937712035240⟩, ⟨.privateRow 4 21, 32466705371100⟩, ⟨.privateRow 5 16, 2090826377640⟩, ⟨.privateRow 5 17, 5777748384408⟩, ⟨.privateRow 5 18, 9044296496235⟩, ⟨.privateRow 5 19, 13472578419300⟩, ⟨.privateRow 5 20, 11838200053680⟩, ⟨.privateRow 6 13, 155607276825⟩, ⟨.privateRow 6 14, 1385406722700⟩, ⟨.privateRow 6 15, 2549951504100⟩, ⟨.privateRow 6 16, 3806856733680⟩, ⟨.privateRow 6 17, 5697234167625⟩, ⟨.privateRow 6 18, 5206987585800⟩, ⟨.privateRow 6 19, 451763061750⟩, ⟨.privateRow 7 11, 199445025780⟩, ⟨.privateRow 7 12, 686679853860⟩, ⟨.privateRow 7 13, 1240842542940⟩, ⟨.privateRow 7 14, 1196670154680⟩, ⟨.privateRow 7 15, 3604466882016⟩, ⟨.privateRow 8 9, 149918408640⟩, ⟨.privateRow 8 10, 362302820880⟩, ⟨.privateRow 8 11, 639495711855⟩, ⟨.privateRow 8 12, 902187566280⟩, ⟨.privateRow 8 13, 270165465570⟩, ⟨.privateRow 9 6, 3904125225⟩, ⟨.privateRow 9 7, 91143577980⟩, ⟨.privateRow 9 8, 197704901394⟩, ⟨.privateRow 9 9, 418522224120⟩, ⟨.privateRow 10 4, 3706773840⟩, ⟨.privateRow 10 5, 57223321155⟩, ⟨.privateRow 10 6, 137993080680⟩, ⟨.privateRow 11 2, 1434168450⟩, ⟨.privateRow 11 3, 41701205700⟩, ⟨.privateRow 11 4, 6692786100⟩, ⟨.privateRow 12 1, 9465511770⟩, ⟨.hall 4 21, 6143977639800⟩, ⟨.hall 3 22, 23818519965240⟩, ⟨.hall 2 23, 53595831088800⟩, ⟨.assumptionRow 13, 31312200920⟩]
  caps := #[0, 296352319120, 8331753804660, 728026399100, 177842522858, 243372981852, 0, 89742640416, 0, 31255130972, 110306457275, 25575527120, 2915665610, 261737699080, 24420825000, 0, 0] }

theorem case_42_26_13_checked :
    (Witness.linear .conditional case_42_26_13).check 42 26 13 = true := by
  change case_42_26_13.check 42 26 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_26_14 : Certificate := {
  objectiveScale := 849057778800000
  eta := 314050774997905545600
  rows := #[⟨.count 2, 63999741268512569520⟩, ⟨.count 3, 13000478510465245800⟩, ⟨.count 4, 2760885934047521280⟩, ⟨.count 5, 581720757884065800⟩, ⟨.count 6, 131912163687704400⟩, ⟨.count 7, 29947626350722080⟩, ⟨.count 8, 6655028077938240⟩, ⟨.count 9, 2495635529226840⟩, ⟨.path 8, 1750147502463360⟩, ⟨.privateRow 2 24, 6899600359802470320⟩, ⟨.privateRow 3 21, 1019645373369823200⟩, ⟨.privateRow 3 22, 2319693224416347780⟩, ⟨.privateRow 4 18, 76865574300186672⟩, ⟨.privateRow 4 19, 577472235495024870⟩, ⟨.privateRow 4 20, 952976252803334760⟩, ⟨.privateRow 4 21, 1523585490592985820⟩, ⟨.privateRow 5 16, 81266607749347020⟩, ⟨.privateRow 5 17, 230858170432193304⟩, ⟨.privateRow 5 18, 391517678620848780⟩, ⟨.privateRow 5 19, 645775403134221360⟩, ⟨.privateRow 5 20, 639239214843389160⟩, ⟨.privateRow 6 13, 1411222471884225⟩, ⟨.privateRow 6 14, 45838203598044000⟩, ⟨.privateRow 6 15, 96953459647344300⟩, ⟨.privateRow 6 16, 161740950251320440⟩, ⟨.privateRow 6 17, 272143112472831600⟩, ⟨.privateRow 6 18, 298287865636160400⟩, ⟨.privateRow 6 19, 188658162030838500⟩, ⟨.privateRow 7 11, 2218342692646080⟩, ⟨.privateRow 7 12, 20455298355627135⟩, ⟨.privateRow 7 13, 44768645514089640⟩, ⟨.privateRow 7 14, 72016910986260240⟩, ⟨.privateRow 7 15, 122143533187587912⟩, ⟨.privateRow 7 16, 140468628359339280⟩, ⟨.privateRow 8 9, 1441922750219952⟩, ⟨.privateRow 8 10, 9243094552692000⟩, ⟨.privateRow 8 11, 21663502857871875⟩, ⟨.privateRow 8 12, 36285748329710880⟩, ⟨.privateRow 8 13, 61235501411584500⟩, ⟨.privateRow 8 14, 21517924118666976⟩, ⟨.privateRow 9 7, 655419431918160⟩, ⟨.privateRow 9 8, 4519873236266388⟩, ⟨.privateRow 9 9, 11338195984635520⟩, ⟨.privateRow 9 10, 20346361884113265⟩, ⟨.privateRow 9 11, 16518730407739560⟩, ⟨.privateRow 10 5, 207969627435570⟩, ⟨.privateRow 10 6, 2365992125111160⟩, ⟨.privateRow 10 7, 6666912056648844⟩, ⟨.privateRow 10 8, 8120718785579400⟩, ⟨.privateRow 11 4, 1287431026982100⟩, ⟨.privateRow 11 5, 3835284038422200⟩, ⟨.privateRow 12 2, 502783714679400⟩, ⟨.privateRow 12 3, 871491772110960⟩, ⟨.privateRow 13 1, 301670228807640⟩, ⟨.hall 5 20, 622494122936400⟩, ⟨.hall 4 21, 412136381683746720⟩, ⟨.hall 3 22, 1254607133320260720⟩, ⟨.hall 2 23, 2736048418542358920⟩, ⟨.assumptionRow 14, 777997202021325⟩]
  caps := #[0, 0, 0, 93124302550379100, 4019050761148566, 1494494852746896, 0, 1282353248412522, 892733580023670, 0, 2429474245555266, 2530892224674450, 0, 476326973213685, 8561638364778675, 849057778800000, 0] }

theorem case_42_26_14_checked :
    (Witness.linear .conditional case_42_26_14).check 42 26 14 = true := by
  change case_42_26_14.check 42 26 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_26_15 : Certificate := {
  objectiveScale := 1754965188900000
  eta := 876745902182864313600
  rows := #[⟨.count 2, 161579773639470186000⟩, ⟨.count 3, 29445655643366802840⟩, ⟨.count 4, 5243429634779175840⟩, ⟨.count 5, 918680987247823800⟩, ⟨.count 6, 147381976563822000⟩, ⟨.count 7, 20633476718935080⟩, ⟨.count 8, 2620124027801280⟩, ⟨.path 7, 11405680090524720⟩, ⟨.privateRow 2 24, 17563018873855455000⟩, ⟨.privateRow 3 21, 2629434825685788120⟩, ⟨.privateRow 3 22, 5780742212194709760⟩, ⟨.privateRow 4 18, 236232253863726120⟩, ⟨.privateRow 4 19, 1337491437316684650⟩, ⟨.privateRow 4 20, 2319090492178540080⟩, ⟨.privateRow 4 21, 3902464193729201100⟩, ⟨.privateRow 5 16, 196602877943231760⟩, ⟨.privateRow 5 17, 509211747217365192⟩, ⟨.privateRow 5 18, 917908986418203780⟩, ⟨.privateRow 5 19, 1643847099870895920⟩, ⟨.privateRow 5 20, 1800305934673886640⟩, ⟨.privateRow 6 13, 7544553562195650⟩, ⟨.privateRow 6 14, 90334123050342600⟩, ⟨.privateRow 6 15, 205048099139984100⟩, ⟨.privateRow 6 16, 365928393239889480⟩, ⟨.privateRow 6 17, 679536184799622150⟩, ⟨.privateRow 6 18, 850604550454058400⟩, ⟨.privateRow 6 19, 672342540705435600⟩, ⟨.privateRow 7 11, 5333823913738320⟩, ⟨.privateRow 7 12, 36477039199545945⟩, ⟨.privateRow 7 13, 87707315032674480⟩, ⟨.privateRow 7 14, 157347805455280440⟩, ⟨.privateRow 7 15, 297458937841953888⟩, ⟨.privateRow 7 16, 402352796019234060⟩, ⟨.privateRow 7 17, 261357371773177680⟩, ⟨.privateRow 8 9, 2194353873283572⟩, ⟨.privateRow 8 10, 14992931936862880⟩, ⟨.privateRow 8 11, 39260920979084805⟩, ⟨.privateRow 8 12, 74439595146997080⟩, ⟨.privateRow 8 13, 133189638079898400⟩, ⟨.privateRow 8 14, 230439908245122576⟩, ⟨.privateRow 9 7, 535934460232080⟩, ⟨.privateRow 9 8, 6321049217070588⟩, ⟨.privateRow 9 9, 18813946144073080⟩, ⟨.privateRow 9 10, 38646829410068880⟩, ⟨.privateRow 9 11, 79165175982852960⟩, ⟨.privateRow 9 12, 50655731204158080⟩, ⟨.privateRow 10 6, 2488267136791800⟩, ⟨.privateRow 10 7, 9685101317051160⟩, ⟨.privateRow 10 8, 22317842165378760⟩, ⟨.privateRow 10 9, 36740221300552770⟩, ⟨.privateRow 11 4, 643334024683350⟩, ⟨.privateRow 11 5, 5104137716496000⟩, ⟨.privateRow 11 6, 14387288188373100⟩, ⟨.privateRow 11 7, 4444853261448600⟩, ⟨.privateRow 12 2, 118769358403080⟩, ⟨.privateRow 12 3, 2316002488860060⟩, ⟨.privateRow 12 4, 5474187700941960⟩, ⟨.privateRow 13 1, 356308075209240⟩, ⟨.privateRow 13 2, 1544001659240040⟩, ⟨.hall 5 20, 194470685175709800⟩, ⟨.hall 4 21, 1318015961842179600⟩, ⟨.hall 3 22, 3458496586190766120⟩, ⟨.hall 2 23, 7130585662785314730⟩, ⟨.assumptionRow 15, 912682181953080⟩]
  caps := #[0, 0, 214360653520462680, 15259138092281160, 29473198925420250, 0, 6221848206073500, 2657364785471682, 1101003875017200, 1200642340169160, 912682181953080, 12485878371848700, 0, 27431810725833360, 84728616199116120, 16636969707046920, 1754965188900000] }

theorem case_42_26_15_checked :
    (Witness.linear .conditional case_42_26_15).check 42 26 15 = true := by
  change case_42_26_15.check 42 26 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_26_16 : Certificate := {
  objectiveScale := 1051214392800000
  eta := 576354547297292563800
  rows := #[⟨.count 2, 119434461400718624160⟩, ⟨.count 3, 23349879050168951280⟩, ⟨.count 4, 4862924088379156800⟩, ⟨.count 5, 954283490461501200⟩, ⟨.count 6, 178259680659060000⟩, ⟨.count 7, 29947626350722080⟩, ⟨.count 8, 4436685385292160⟩, ⟨.path 8, 3404147332185600⟩, ⟨.privateRow 4 18, 7059083354098776⟩, ⟨.privateRow 4 19, 850031287222727610⟩, ⟨.privateRow 5 16, 65579755851349740⟩, ⟨.privateRow 5 17, 354784300426371816⟩, ⟨.privateRow 5 18, 698391718875420570⟩, ⟨.privateRow 6 14, 44564920164765000⟩, ⟨.privateRow 6 15, 134387992585746900⟩, ⟨.privateRow 6 17, 1086938402818618350⟩, ⟨.privateRow 6 18, 35057737196281800⟩, ⟨.privateRow 7 11, 871491772110960⟩, ⟨.privateRow 7 12, 20143343914473780⟩, ⟨.privateRow 7 13, 55362363678970920⟩, ⟨.privateRow 7 14, 113670256366927260⟩, ⟨.privateRow 7 15, 106028858056008888⟩, ⟨.privateRow 7 16, 593069957552692620⟩, ⟨.privateRow 7 17, 307082009882007360⟩, ⟨.privateRow 8 9, 305022120238836⟩, ⟨.privateRow 8 10, 9027422346462520⟩, ⟨.privateRow 8 12, 96656360179579200⟩, ⟨.privateRow 8 16, 876152932649674680⟩, ⟨.privateRow 9 7, 252084396891600⟩, ⟨.privateRow 9 8, 3188867620678740⟩, ⟨.privateRow 9 14, 377048934540688410⟩, ⟨.privateRow 10 5, 59419893553020⟩, ⟨.privateRow 10 6, 162054255144600⟩, ⟨.privateRow 10 11, 2376795742120800⟩, ⟨.privateRow 10 14, 130961445390856080⟩, ⟨.privateRow 11 3, 45707610425400⟩, ⟨.privateRow 12 11, 20262183701579820⟩, ⟨.privateRow 13 10, 8823854192623470⟩, ⟨.privateRow 13 12, 1960856487249660⟩, ⟨.hall 12 2, 129287240917560⟩, ⟨.hall 10 5, 106651090992600⟩, ⟨.hall 11 5, 20459597047560⟩, ⟨.hall 13 5, 13204420789560⟩, ⟨.hall 9 6, 49145283646470⟩, ⟨.hall 10 6, 8829879286725⟩, ⟨.hall 8 11, 12497396750300⟩, ⟨.hall 5 15, 140004966891075⟩, ⟨.hall 6 17, 1904563956515220⟩, ⟨.hall 4 18, 4258932039565632⟩, ⟨.hall 3 20, 39112314529036320⟩]
  caps := #[0, 505138204909938600, 96077649115974240, 43713116019727440, 8862447393875790, 0, 1792122394083450, 961998599000868, 0, 2236781948745240, 778483985958900, 0, 14972525437729860, 0, 32255882914432320, 46253433283200000, 9460929535200000] }

theorem case_42_26_16_checked :
    (Witness.linear .negative case_42_26_16).check 42 26 16 = true := by
  change case_42_26_16.check 42 26 16 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_27_1_checked :
    (Witness.rising).check 42 27 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_27_2_checked :
    (Witness.rising).check 42 27 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_27_3_checked :
    (Witness.rising).check 42 27 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_27_4_checked :
    (Witness.rising).check 42 27 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_27_5_checked :
    (Witness.rising).check 42 27 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_27_6_checked :
    (Witness.rising).check 42 27 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_27_7_checked :
    (Witness.rising).check 42 27 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_27_8_checked :
    (Witness.rising).check 42 27 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_27_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_42_27_9_checked :
    (Witness.linear .positive case_42_27_9).check 42 27 9 = true := by
  change case_42_27_9.check 42 27 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_27_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_42_27_10_checked :
    (Witness.linear .positive case_42_27_10).check 42 27 10 = true := by
  change case_42_27_10.check 42 27 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_27_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_42_27_11_checked :
    (Witness.linear .positive case_42_27_11).check 42 27 11 = true := by
  change case_42_27_11.check 42 27 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_27_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_42_27_12_checked :
    (Witness.linear .positive case_42_27_12).check 42 27 12 = true := by
  change case_42_27_12.check 42 27 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_27_13 : Certificate := {
  objectiveScale := 9808814900000
  eta := 23618926352772238488
  rows := #[⟨.count 2, 3307152041596963560⟩, ⟨.count 3, 453083049905250996⟩, ⟨.count 4, 60539881579379664⟩, ⟨.count 5, 8050516167470700⟩, ⟨.count 6, 1405181003776704⟩, ⟨.count 7, 409844459434872⟩, ⟨.count 8, 136614819811624⟩, ⟨.count 9, 87823812736044⟩, ⟨.path 5, 1848137141485635⟩, ⟨.path 6, 141696931996620⟩]
  caps := #[0, 1714105259655502, 0, 252728393517369, 60549830984896, 0, 31279495019916, 2125766365128, 708588788376, 0, 19617629800000, 9808814900000, 9808814900000, 0, 0, 0] }

theorem case_42_27_13_checked :
    (Witness.linear .positive case_42_27_13).check 42 27 13 = true := by
  change case_42_27_13.check 42 27 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_27_14 : Certificate := {
  objectiveScale := 448765214554800000
  eta := 494294100019142118696000
  rows := #[⟨.count 2, 79706132762382212486400⟩, ⟨.count 3, 12947037995383219728000⟩, ⟨.count 4, 2187602971633716436800⟩, ⟨.count 5, 358512546371635656000⟩, ⟨.count 6, 60879489006504168000⟩, ⟨.count 7, 12626856979126790400⟩, ⟨.count 8, 3156714244781697600⟩, ⟨.path 6, 6528264567512688000⟩, ⟨.path 7, 2717664937743712320⟩, ⟨.privateRow 2 25, 7158075029631412286400⟩, ⟨.privateRow 3 21, 111612396511924308000⟩, ⟨.privateRow 3 22, 1607218509771710035200⟩, ⟨.privateRow 3 23, 2410827764657565052800⟩, ⟨.privateRow 4 19, 334093106892360095280⟩, ⟨.privateRow 4 20, 700367788112325032700⟩, ⟨.privateRow 4 21, 990870053478083578800⟩, ⟨.privateRow 4 22, 1395154956399053850000⟩, ⟨.privateRow 5 16, 43678617509428387200⟩, ⟨.privateRow 5 17, 171815446751689540800⟩, ⟨.privateRow 5 18, 283833706523657209920⟩, ⟨.privateRow 5 19, 401466408059558041200⟩, ⟨.privateRow 5 20, 587599808707221710400⟩, ⟨.privateRow 5 21, 463360555216170612000⟩, ⟨.privateRow 6 13, 2630595203984748000⟩, ⟨.privateRow 6 14, 32046286574257055100⟩, ⟨.privateRow 6 15, 76534214751033811200⟩, ⟨.privateRow 6 16, 125366651435615990400⟩, ⟨.privateRow 6 17, 126764624886876456480⟩, ⟨.privateRow 6 18, 343292674120009614000⟩, ⟨.privateRow 6 19, 100338417066275388000⟩, ⟨.privateRow 7 11, 2615563231390549440⟩, ⟨.privateRow 7 12, 17587407935212315200⟩, ⟨.privateRow 7 13, 37204132170641436000⟩, ⟨.privateRow 7 14, 60428529828678211200⟩, ⟨.privateRow 7 15, 83277128171860022400⟩, ⟨.privateRow 7 16, 96956223232580712000⟩, ⟨.privateRow 8 9, 1685972380735679400⟩, ⟨.privateRow 8 10, 9588519518524406460⟩, ⟨.privateRow 8 11, 20562485844480780200⟩, ⟨.privateRow 8 12, 33392117870581394925⟩, ⟨.privateRow 8 13, 39684407648684198400⟩, ⟨.privateRow 9 7, 977078218622906400⟩, ⟨.privateRow 9 8, 5739480445057632000⟩, ⟨.privateRow 9 9, 13122912074735342880⟩, ⟨.privateRow 9 10, 15332612046082531200⟩, ⟨.privateRow 10 5, 572371264163714400⟩, ⟨.privateRow 10 6, 3889522908748877400⟩, ⟨.privateRow 10 7, 6518409934029739200⟩, ⟨.privateRow 11 3, 386536438136534400⟩, ⟨.privateRow 11 4, 2705755066955740800⟩, ⟨.privateRow 12 1, 248027547804276240⟩, ⟨.privateRow 12 2, 531487602437734800⟩, ⟨.hall 4 22, 106112655234525139200⟩, ⟨.hall 3 23, 777566362366406012400⟩, ⟨.hall 2 24, 2220937874058611163456⟩, ⟨.assumptionRow 14, 440018372554750080⟩]
  caps := #[0, 758865399732402955200, 0, 0, 9667875811030016580, 0, 377110308007877340, 0, 327530536345826580, 1781540484010996800, 4444964531345331000, 954374022953208000, 0, 28834682677507848960, 4945164202102849920, 448765214554800000] }

theorem case_42_27_14_checked :
    (Witness.linear .conditional case_42_27_14).check 42 27 14 = true := by
  change case_42_27_14.check 42 27 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_27_15 : Certificate := {
  objectiveScale := 2519737308000000
  eta := 3266957305395989805600
  rows := #[⟨.count 2, 496362867018236618400⟩, ⟨.count 3, 74299639137864940800⟩, ⟨.count 4, 10862520341793120000⟩, ⟨.count 5, 1407190135186836000⟩, ⟨.count 6, 162937805126896800⟩, ⟨.count 7, 23041709815924800⟩, ⟨.count 8, 11520854907962400⟩, ⟨.path 6, 95595473269296000⟩, ⟨.privateRow 2 25, 47306276088509037600⟩, ⟨.privateRow 3 21, 529547866662414600⟩, ⟨.privateRow 3 22, 9848685109892428800⟩, ⟨.privateRow 3 23, 15723498194745541200⟩, ⟨.privateRow 4 19, 1781453336054071680⟩, ⟨.privateRow 4 20, 4195648482017592600⟩, ⟨.privateRow 4 21, 6422465152085182200⟩, ⟨.privateRow 4 22, 9769479232400187300⟩, ⟨.privateRow 5 16, 196795011387031200⟩, ⟨.privateRow 5 17, 893689173574797600⟩, ⟨.privateRow 5 18, 1648140586404792480⟩, ⟨.privateRow 5 19, 2573676694618029000⟩, ⟨.privateRow 5 20, 4180424495174928000⟩, ⟨.privateRow 5 21, 3883351022191040400⟩, ⟨.privateRow 6 13, 7131957800167200⟩, ⟨.privateRow 6 14, 134547126960846600⟩, ⟨.privateRow 6 15, 382304287354017600⟩, ⟨.privateRow 6 16, 704006526697273800⟩, ⟨.privateRow 6 17, 1083289528631550240⟩, ⟨.privateRow 6 18, 1492979358340770300⟩, ⟨.privateRow 6 19, 2560098544190787600⟩, ⟨.privateRow 7 11, 4772925604727280⟩, ⟨.privateRow 7 12, 68393646596475200⟩, ⟨.privateRow 7 13, 174664389586787100⟩, ⟨.privateRow 7 14, 325640490765876000⟩, ⟨.privateRow 7 15, 509112064504243200⟩, ⟨.privateRow 7 16, 855505768736979360⟩, ⟨.privateRow 7 17, 614719901160565200⟩, ⟨.privateRow 8 9, 1309188057723000⟩, ⟨.privateRow 8 10, 33554489919440490⟩, ⟨.privateRow 8 11, 89286625536708600⟩, ⟨.privateRow 8 12, 169572583176571575⟩, ⟨.privateRow 8 13, 271563008544828000⟩, ⟨.privateRow 8 14, 414270741065481300⟩, ⟨.privateRow 9 8, 16458364154232000⟩, ⟨.privateRow 9 9, 51514679802746160⟩, ⟨.privateRow 9 10, 103139082033187200⟩, ⟨.privateRow 9 11, 170138339444373300⟩, ⟨.privateRow 9 12, 21866112376336800⟩, ⟨.privateRow 10 6, 8023452525188100⟩, ⟨.privateRow 10 7, 33440403531553200⟩, ⟨.privateRow 10 8, 74556389618670960⟩, ⟨.privateRow 10 9, 11795160977199600⟩, ⟨.privateRow 11 4, 4177892439151200⟩, ⟨.privateRow 11 5, 23864628023636400⟩, ⟨.privateRow 11 6, 14363663261875200⟩, ⟨.privateRow 12 2, 2909603662980300⟩, ⟨.privateRow 12 3, 9400257988090200⟩, ⟨.privateRow 13 0, 3620840113931040⟩, ⟨.hall 4 22, 1447548906417213600⟩, ⟨.hall 3 23, 6110167692258630000⟩, ⟨.hall 2 24, 15448676430098175264⟩, ⟨.assumptionRow 15, 1596555953094960⟩]
  caps := #[0, 3051053174832458400, 422270265728124000, 69507394124425488, 9511025966261820, 18610768221233760, 11197373752207500, 0, 0, 8158485798981480, 1596555953094960, 701293287562560, 77258988462674700, 0, 144624253582860480, 26120554434905040] }

theorem case_42_27_15_checked :
    (Witness.linear .conditional case_42_27_15).check 42 27 15 = true := by
  change case_42_27_15.check 42 27 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_27_16 : Certificate := {
  objectiveScale := 8331803552358000000
  eta := 18830989030640261032958400
  rows := #[⟨.count 2, 2687888240434772841866400⟩, ⟨.count 3, 370713324282028442114400⟩, ⟨.count 4, 47314042790553419680800⟩, ⟨.count 5, 5120567401575045420000⟩, ⟨.count 6, 378134208116311046400⟩, ⟨.path 5, 716093137873037925000⟩, ⟨.path 6, 376292322568003842000⟩, ⟨.privateRow 2 25, 250088511892925218312800⟩, ⟨.privateRow 3 21, 5849263531799186499000⟩, ⟨.privateRow 3 22, 50722502527601834529600⟩, ⟨.privateRow 3 23, 81456410665055337912000⟩, ⟨.privateRow 4 18, 1068754324328740249200⟩, ⟨.privateRow 4 19, 9558129889740004012440⟩, ⟨.privateRow 4 20, 21068180683980403223250⟩, ⟨.privateRow 4 21, 32698105274057674651200⟩, ⟨.privateRow 4 22, 50931920604666249848700⟩, ⟨.privateRow 5 15, 110289144033924055200⟩, ⟨.privateRow 5 16, 1499032039318233076800⟩, ⟨.privateRow 5 17, 4461458469372308804400⟩, ⟨.privateRow 5 18, 8104676527292933427840⟩, ⟨.privateRow 5 19, 12836868585948517710600⟩, ⟨.privateRow 5 20, 21606168502645883956800⟩, ⟨.privateRow 5 21, 21159760062508572304800⟩, ⟨.privateRow 6 12, 7090016402180832120⟩, ⟨.privateRow 6 13, 172436201386373324400⟩, ⟨.privateRow 6 14, 806489365748069653650⟩, ⟨.privateRow 6 15, 1876040848005626530800⟩, ⟨.privateRow 6 16, 3370383723036702972600⟩, ⟨.privateRow 6 17, 5290727795227385390880⟩, ⟨.privateRow 6 18, 9185510138825389168800⟩, ⟨.privateRow 6 19, 10532613255239747271600⟩, ⟨.privateRow 6 20, 3682869631132821129000⟩, ⟨.privateRow 7 9, 875310666935905200⟩, ⟨.privateRow 7 10, 11458612367160940800⟩, ⟨.privateRow 7 11, 109238771233600968960⟩, ⟨.privateRow 7 12, 389805017008789782400⟩, ⟨.privateRow 7 13, 850801968261699854400⟩, ⟨.privateRow 7 14, 1529042690756035540800⟩, ⟨.privateRow 7 15, 2424610547412457404000⟩, ⟨.privateRow 7 16, 4263463196511407048160⟩, ⟨.privateRow 7 17, 4553366089400578850400⟩, ⟨.privateRow 8 7, 706981692525154200⟩, ⟨.privateRow 8 8, 8041916752473629025⟩, ⟨.privateRow 8 9, 63499810201350213600⟩, ⟨.privateRow 8 10, 201737225962052750970⟩, ⟨.privateRow 8 11, 437071793023328663200⟩, ⟨.privateRow 8 12, 788107841742415644450⟩, ⟨.privateRow 8 13, 1265042741389116990300⟩, ⟨.privateRow 8 14, 2265522833696856633900⟩, ⟨.privateRow 8 15, 636919806795911418780⟩, ⟨.privateRow 9 5, 750266285945061600⟩, ⟨.privateRow 9 6, 6059843078787036000⟩, ⟨.privateRow 9 7, 39826635345583686600⟩, ⟨.privateRow 9 8, 120792872037154917600⟩, ⟨.privateRow 9 9, 264168759281256189360⟩, ⟨.privateRow 9 10, 482004407259371796800⟩, ⟨.privateRow 9 11, 783184219240901177700⟩, ⟨.privateRow 9 12, 490674151008070286400⟩, ⟨.privateRow 10 3, 525186400161543120⟩, ⟨.privateRow 10 4, 5064297430129165800⟩, ⟨.privateRow 10 5, 29693231086056476400⟩, ⟨.privateRow 10 6, 87968722027058472600⟩, ⟨.privateRow 10 7, 135354858587088613200⟩, ⟨.privateRow 10 8, 482908894948538898840⟩, ⟨.privateRow 10 9, 56895193350833838000⟩, ⟨.privateRow 11 1, 984724500302893350⟩, ⟨.privateRow 11 2, 5251864001615431200⟩, ⟨.privateRow 11 3, 28134985722939810000⟩, ⟨.privateRow 11 4, 82413865871503689600⟩, ⟨.privateRow 11 5, 161494818049674509400⟩, ⟨.privateRow 12 0, 10831969503331826850⟩, ⟨.privateRow 12 1, 34662302410661845920⟩, ⟨.privateRow 12 2, 49517574872374065600⟩, ⟨.privateRow 13 0, 34662302410661845920⟩, ⟨.hall 4 22, 8680646168930966630400⟩, ⟨.hall 3 23, 32950851229135417277700⟩, ⟨.hall 2 24, 81380153599751881850976⟩]
  caps := #[0, 11836733683937578930800, 387989783080434077400, 475139108667385377072, 60878816944817543100, 19383768038100609000, 15492391766548489650, 6626163368072356760, 93565684980131841775, 0, 92277676438608887640, 181380221914729711500, 0, 0, 1733015138890464000000, 449917391827332000000] }

theorem case_42_27_16_checked :
    (Witness.linear .negative case_42_27_16).check 42 27 16 = true := by
  change case_42_27_16.check 42 27 16 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_27_17 : Certificate := {
  objectiveScale := 26139093084000000
  eta := 66611331902789580947040
  rows := #[⟨.count 2, 8545349227522495227840⟩, ⟨.count 3, 1047787849649022562080⟩, ⟨.count 4, 118423196766228594240⟩, ⟨.count 5, 11701896913658952000⟩, ⟨.count 6, 936151753092716160⟩, ⟨.path 4, 18484388781617959200⟩, ⟨.path 6, 926684100396054000⟩, ⟨.privateRow 7 10, 2364019578516960⟩, ⟨.privateRow 7 12, 179140150283174080⟩, ⟨.hall 11 6, 2036044334794140⟩, ⟨.hall 10 8, 1123176722824800⟩, ⟨.hall 8 9, 1013392531872000⟩, ⟨.hall 9 9, 1084667806613664⟩, ⟨.hall 12 9, 4972234586023584⟩, ⟨.hall 7 10, 886841620730415⟩, ⟨.hall 11 11, 196460418269610⟩, ⟨.hall 6 13, 1587309497072442⟩, ⟨.hall 5 15, 3262485555546750⟩, ⟨.hall 4 17, 22669033770240⟩]
  caps := #[0, 11151737601219689760, 0, 0, 0, 31327274481750000, 0, 45816950878876320, 0, 67259023196302080, 0, 0, 1485722264319853560, 451451413344934080, 11213670933036000000, 4025420334936000000] }

theorem case_42_27_17_checked :
    (Witness.linear .negative case_42_27_17).check 42 27 17 = true := by
  change case_42_27_17.check 42 27 17 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_28_1_checked :
    (Witness.rising).check 42 28 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_28_2_checked :
    (Witness.rising).check 42 28 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_28_3_checked :
    (Witness.rising).check 42 28 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_28_4_checked :
    (Witness.rising).check 42 28 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_28_5_checked :
    (Witness.rising).check 42 28 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_28_6_checked :
    (Witness.rising).check 42 28 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_28_7_checked :
    (Witness.rising).check 42 28 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_28_8_checked :
    (Witness.rising).check 42 28 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_28_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_42_28_9_checked :
    (Witness.linear .positive case_42_28_9).check 42 28 9 = true := by
  change case_42_28_9.check 42 28 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_28_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_42_28_10_checked :
    (Witness.linear .positive case_42_28_10).check 42 28 10 = true := by
  change case_42_28_10.check 42 28 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_28_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_42_28_11_checked :
    (Witness.linear .positive case_42_28_11).check 42 28 11 = true := by
  change case_42_28_11.check 42 28 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_28_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_42_28_12_checked :
    (Witness.linear .positive case_42_28_12).check 42 28 12 = true := by
  change case_42_28_12.check 42 28 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_28_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_42_28_13_checked :
    (Witness.linear .positive case_42_28_13).check 42 28 13 = true := by
  change case_42_28_13.check 42 28 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_28_14 : Certificate := {
  objectiveScale := 16280082000000
  eta := 41169247166949501600
  rows := #[⟨.count 2, 5912262141137352000⟩, ⟨.count 3, 848790109371204000⟩, ⟨.count 4, 119203125077836800⟩, ⟨.count 5, 17561174676645600⟩, ⟨.count 6, 1064313616766400⟩, ⟨.count 7, 310424804890200⟩, ⟨.path 6, 1003007696090400⟩, ⟨.privateRow 2 26, 456590541592785600⟩, ⟨.privateRow 3 22, 34634538945606600⟩, ⟨.privateRow 3 23, 113172014582827200⟩, ⟨.privateRow 3 24, 152684657605279800⟩, ⟨.privateRow 4 19, 9268397746007400⟩, ⟨.privateRow 4 20, 30652232162872320⟩, ⟨.privateRow 4 21, 48825387169158600⟩, ⟨.privateRow 4 22, 61818882573848400⟩, ⟨.privateRow 4 23, 78493129236522000⟩, ⟨.privateRow 5 16, 1543254744311280⟩, ⟨.privateRow 5 17, 7450195317364800⟩, ⟨.privateRow 5 18, 14332756705787520⟩, ⟨.privateRow 5 19, 20307103807902912⟩, ⟨.privateRow 5 20, 25330664079040320⟩, ⟨.privateRow 5 21, 32816336516964000⟩, ⟨.privateRow 5 22, 8887018699999440⟩, ⟨.privateRow 6 6, 24347043520800⟩, ⟨.privateRow 6 13, 82779947970720⟩, ⟨.privateRow 6 14, 1458503845198400⟩, ⟨.privateRow 6 15, 4072477797488100⟩, ⟨.privateRow 6 16, 6723759039254400⟩, ⟨.privateRow 6 17, 9371872680970800⟩, ⟨.privateRow 6 18, 11399981406253440⟩, ⟨.privateRow 6 19, 8204084129241000⟩, ⟨.privateRow 7 11, 120944729178000⟩, ⟨.privateRow 7 12, 997794015718500⟩, ⟨.privateRow 7 13, 2261666435628600⟩, ⟨.privateRow 7 14, 3614231656935900⟩, ⟨.privateRow 7 15, 4954126478043600⟩, ⟨.privateRow 7 16, 2653392975132900⟩, ⟨.privateRow 8 9, 96083868180300⟩, ⟨.privateRow 8 10, 685353465342000⟩, ⟨.privateRow 8 11, 1144137138023880⟩, ⟨.privateRow 8 12, 2946571957529200⟩, ⟨.privateRow 8 13, 77606201222550⟩, ⟨.privateRow 9 7, 77321929423200⟩, ⟨.privateRow 9 8, 527229430527800⟩, ⟨.privateRow 9 9, 994434439908000⟩, ⟨.privateRow 10 5, 76022401197600⟩, ⟨.privateRow 10 6, 409351391064000⟩, ⟨.privateRow 11 3, 88692801397200⟩, ⟨.privateRow 11 4, 38011200598800⟩, ⟨.privateRow 12 1, 60976300960575⟩, ⟨.hall 3 24, 24585644547303840⟩, ⟨.hall 2 25, 109869913361577600⟩, ⟨.assumptionRow 14, 17077806018000⟩]
  caps := #[0, 65673652354783200, 0, 2454030006966720, 585198614342160, 101289160260288, 0, 669102299868600, 141408792252000, 304080187919200, 17077806018000, 2091678269522400, 0, 1226118095748000, 194563259982000] }

theorem case_42_28_14_checked :
    (Witness.linear .conditional case_42_28_14).check 42 28 14 = true := by
  change case_42_28_14.check 42 28 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_28_15 : Certificate := {
  objectiveScale := 29557944000000
  eta := 101707851588803460000
  rows := #[⟨.count 2, 12678001965488059200⟩, ⟨.count 3, 1488318830047249200⟩, ⟨.count 4, 156142806797577600⟩, ⟨.count 5, 13232441254032000⟩, ⟨.count 6, 882162750268800⟩, ⟨.count 7, 771892406485200⟩, ⟨.count 8, 441081375134400⟩, ⟨.path 5, 9548808273576000⟩, ⟨.privateRow 2 26, 1011620133870746400⟩, ⟨.privateRow 3 22, 78236808914464200⟩, ⟨.privateRow 3 23, 232890966070963200⟩, ⟨.privateRow 3 24, 334174276836199800⟩, ⟨.privateRow 4 19, 18249741896185800⟩, ⟨.privateRow 4 20, 58487390342821440⟩, ⟨.privateRow 4 21, 98416281826863000⟩, ⟨.privateRow 4 22, 135632522853828000⟩, ⟨.privateRow 4 23, 188066071322929800⟩, ⟨.privateRow 5 16, 2398379977293300⟩, ⟨.privateRow 5 17, 12533012216318880⟩, ⟨.privateRow 5 18, 26067909270443040⟩, ⟨.privateRow 5 19, 40544200002354048⟩, ⟨.privateRow 5 20, 55907064298285200⟩, ⟨.privateRow 5 21, 81644162537377440⟩, ⟨.privateRow 5 22, 53922198110180400⟩, ⟨.privateRow 6 12, 40098306830400⟩, ⟨.privateRow 6 14, 1919520799196000⟩, ⟨.privateRow 6 15, 6441625916025300⟩, ⟨.privateRow 6 16, 11877691316119200⟩, ⟨.privateRow 6 17, 18427399672281600⟩, ⟨.privateRow 6 18, 25171043807669760⟩, ⟨.privateRow 6 19, 37491916886424000⟩, ⟨.privateRow 6 20, 6640725147856800⟩, ⟨.privateRow 7 12, 1196433230052060⟩, ⟨.privateRow 7 13, 3393876136450800⟩, ⟨.privateRow 7 14, 6168247355395125⟩, ⟨.privateRow 7 15, 9499002471644400⟩, ⟨.privateRow 7 16, 13067035738356600⟩, ⟨.privateRow 7 17, 8512870540093920⟩, ⟨.privateRow 8 10, 721769522947200⟩, ⟨.privateRow 8 11, 2045514877185780⟩, ⟨.privateRow 8 12, 3773696209483200⟩, ⟨.privateRow 8 13, 5844328220530800⟩, ⟨.privateRow 8 14, 3040310907176400⟩, ⟨.privateRow 9 8, 477838156395600⟩, ⟨.privateRow 9 9, 1470271250448000⟩, ⟨.privateRow 9 10, 2830272157112400⟩, ⟨.privateRow 9 11, 710631104383200⟩, ⟨.privateRow 10 6, 376615635691680⟩, ⟨.privateRow 10 7, 1301190056646480⟩, ⟨.privateRow 10 8, 192471872785920⟩, ⟨.privateRow 11 4, 354440390733000⟩, ⟨.privateRow 11 5, 229023021704400⟩, ⟨.privateRow 12 2, 161729837549280⟩, ⟨.hall 3 24, 72487313189587296⟩, ⟨.hall 2 25, 257523664405392000⟩, ⟨.assumptionRow 15, 21574632479400⟩]
  caps := #[0, 0, 6127870450478400, 3771718282807200, 0, 630620229154032, 57856430431800, 0, 0, 506929491837600, 21574632479400, 1658140074500400, 417828603235680, 8403563476854000, 1995491465767800] }

theorem case_42_28_15_checked :
    (Witness.linear .conditional case_42_28_15).check 42 28 15 = true := by
  change case_42_28_15.check 42 28 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_28_16 : Certificate := {
  objectiveScale := 162279531774360000
  eta := 730337117852032242552000
  rows := #[⟨.count 2, 90948550958661789993600⟩, ⟨.count 3, 10548778113577553850000⟩, ⟨.count 4, 1060905684565513987200⟩, ⟨.count 5, 76718386280564028000⟩, ⟨.count 6, 1461302595820267200⟩, ⟨.path 5, 66096916497241344000⟩, ⟨.path 6, 840244266724777200⟩, ⟨.privateRow 2 26, 7595120241775838772000⟩, ⟨.privateRow 3 22, 516387804797986921800⟩, ⟨.privateRow 3 23, 1681106861274899058000⟩, ⟨.privateRow 3 24, 2501567381219819913000⟩, ⟨.privateRow 4 19, 122566755224424911400⟩, ⟨.privateRow 4 20, 395866873207710384480⟩, ⟨.privateRow 4 21, 702521222940593456400⟩, ⟨.privateRow 4 22, 1012317373254490102800⟩, ⟨.privateRow 4 23, 1475184970480559738400⟩, ⟨.privateRow 5 15, 243550432636711200⟩, ⟨.privateRow 5 16, 18357613859992106700⟩, ⟨.privateRow 5 17, 81791193863197241280⟩, ⟨.privateRow 5 18, 174114204291984836880⟩, ⟨.privateRow 5 19, 283638833848713863520⟩, ⟨.privateRow 5 20, 412964113578807510720⟩, ⟨.privateRow 5 21, 644580575016319861920⟩, ⟨.privateRow 5 22, 531768014618995234080⟩, ⟨.privateRow 6 12, 199268535793672800⟩, ⟨.privateRow 6 13, 1607432855402293920⟩, ⟨.privateRow 6 14, 13314090317473545600⟩, ⟨.privateRow 6 15, 40794697466649126000⟩, ⟨.privateRow 6 16, 77414244659526060000⟩, ⟨.privateRow 6 17, 125631431501770194000⟩, ⟨.privateRow 6 18, 158259071127334937760⟩, ⟨.privateRow 6 19, 341092380907714035600⟩, ⟨.privateRow 6 20, 144750140463752023200⟩, ⟨.privateRow 7 10, 136997118358150050⟩, ⟨.privateRow 7 11, 1328456905291152000⟩, ⟨.privateRow 7 12, 8037164277011469600⟩, ⟨.privateRow 7 13, 21026520684302733600⟩, ⟨.privateRow 7 14, 38975680172893689225⟩, ⟨.privateRow 7 15, 62862106309482565800⟩, ⟨.privateRow 7 16, 91818513104040122400⟩, ⟨.privateRow 7 17, 135207022678270222680⟩, ⟨.privateRow 8 8, 98356905487902600⟩, ⟨.privateRow 8 9, 1004645534626433700⟩, ⟨.privateRow 8 10, 5131164796687074600⟩, ⟨.privateRow 8 11, 12530669759158791240⟩, ⟨.privateRow 8 12, 23198178708646741800⟩, ⟨.privateRow 8 13, 37377380458715271975⟩, ⟨.privateRow 8 14, 54851036721682172400⟩, ⟨.privateRow 8 15, 5479884734326002000⟩, ⟨.privateRow 9 6, 86982297370254000⟩, ⟨.privateRow 9 7, 843059189896308000⟩, ⟨.privateRow 9 8, 3815623444641808800⟩, ⟨.privateRow 9 9, 9188493594930468000⟩, ⟨.privateRow 9 10, 17097240371097126240⟩, ⟨.privateRow 9 11, 21405376912848728800⟩, ⟨.privateRow 10 4, 116904207665621376⟩, ⟨.privateRow 10 5, 876781557492160320⟩, ⟨.privateRow 10 6, 3574570965160345920⟩, ⟨.privateRow 10 7, 8658217880235083160⟩, ⟨.privateRow 10 8, 5858494952333980320⟩, ⟨.privateRow 11 2, 136997118358150050⟩, ⟨.privateRow 11 3, 1169042076656213760⟩, ⟨.privateRow 11 4, 4462191855094030200⟩, ⟨.privateRow 11 5, 758753270906677200⟩, ⟨.privateRow 12 0, 236387184617984400⟩, ⟨.privateRow 12 1, 1758129685596258975⟩, ⟨.hall 4 23, 23015515884169208400⟩, ⟨.hall 3 24, 624969894180411876096⟩, ⟨.hall 2 25, 1999399174758084052800⟩, ⟨.assumptionRow 16, 40697824696963200⟩]
  caps := #[0, 0, 4842860380501010400, 0, 2708467987556490120, 287424958538250000, 0, 893970015820325730, 0, 1762995438756312320, 0, 0, 0, 133430135270730480000, 41168579672734113600] }

theorem case_42_28_16_checked :
    (Witness.linear .conditional case_42_28_16).check 42 28 16 = true := by
  change case_42_28_16.check 42 28 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_28_17 : Certificate := {
  objectiveScale := 81959359482000000
  eta := 380527579859385039681600
  rows := #[⟨.count 2, 52852392285627424089600⟩, ⟨.count 3, 6992332920999978552000⟩, ⟨.count 4, 846094202979934708800⟩, ⟨.count 5, 85486201855485631200⟩, ⟨.count 6, 5845210383281068800⟩, ⟨.path 5, 12469270266831549600⟩, ⟨.path 6, 5674464632385291600⟩, ⟨.privateRow 6 14, 1840158824366262400⟩, ⟨.privateRow 6 17, 75825368027562753600⟩, ⟨.privateRow 7 11, 83028556580697000⟩, ⟨.privateRow 7 12, 1242107206447227120⟩, ⟨.privateRow 7 19, 52119792584256196800⟩, ⟨.privateRow 8 9, 45665706119383350⟩, ⟨.privateRow 8 10, 714045586593994200⟩, ⟨.privateRow 10 8, 39853707158734560⟩, ⟨.hall 9 6, 96946213787280⟩, ⟨.hall 9 7, 4367551221134640⟩, ⟨.hall 10 7, 3409430547374775⟩, ⟨.hall 11 7, 2686218007022550⟩, ⟨.hall 12 7, 2107647974740770⟩, ⟨.hall 8 8, 3663793521049200⟩, ⟨.hall 7 9, 3040133832354960⟩, ⟨.hall 6 11, 2205888876212175⟩, ⟨.hall 5 15, 6399535805371800⟩, ⟨.hall 4 18, 73431009144628200⟩, ⟨.hall 3 20, 387835154778882096⟩, ⟨.hall 2 23, 17112977475975190656⟩]
  caps := #[0, 0, 0, 6272897483534220000, 0, 444066111058026600, 0, 370307362349908620, 0, 73703014327580400, 158046852416675040, 6968635519636791000, 0, 2641586218223032080, 52208111990034000000] }

theorem case_42_28_17_checked :
    (Witness.linear .negative case_42_28_17).check 42 28 17 = true := by
  change case_42_28_17.check 42 28 17 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_28_18 : Certificate := {
  objectiveScale := 13
  eta := 11305
  rows := #[⟨.assumptionRow 18, 5⟩]
  caps := #[0, 0, 5130, 2601, 1428, 580, 364, 195, 90, 58, 3536, 27846, 26416, 17836, 9828] }

theorem case_42_28_18_checked :
    (Witness.linear .conditional case_42_28_18).check 42 28 18 = true := by
  change case_42_28_18.check 42 28 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_29_1_checked :
    (Witness.rising).check 42 29 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_29_2_checked :
    (Witness.rising).check 42 29 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_29_3_checked :
    (Witness.rising).check 42 29 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_29_4_checked :
    (Witness.rising).check 42 29 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_29_5_checked :
    (Witness.rising).check 42 29 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_29_6_checked :
    (Witness.rising).check 42 29 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_29_7_checked :
    (Witness.rising).check 42 29 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_29_8_checked :
    (Witness.rising).check 42 29 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_29_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_42_29_9_checked :
    (Witness.linear .positive case_42_29_9).check 42 29 9 = true := by
  change case_42_29_9.check 42 29 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_29_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_42_29_10_checked :
    (Witness.linear .positive case_42_29_10).check 42 29 10 = true := by
  change case_42_29_10.check 42 29 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_29_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_42_29_11_checked :
    (Witness.linear .positive case_42_29_11).check 42 29 11 = true := by
  change case_42_29_11.check 42 29 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_29_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_42_29_12_checked :
    (Witness.linear .positive case_42_29_12).check 42 29 12 = true := by
  change case_42_29_12.check 42 29 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_29_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_42_29_13_checked :
    (Witness.linear .positive case_42_29_13).check 42 29 13 = true := by
  change case_42_29_13.check 42 29 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_29_14 : Certificate := {
  objectiveScale := 821
  eta := 121263890
  rows := #[⟨.assumptionRow 14, 1790⟩]
  caps := #[0, 0, 35384650, 10475400, 3154840, 969969, 305855, 100815, 35772, 13566, 1160862, 655554, 233614, 58534] }

theorem case_42_29_14_checked :
    (Witness.linear .conditional case_42_29_14).check 42 29 14 = true := by
  change case_42_29_14.check 42 29 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_29_15 : Certificate := {
  objectiveScale := 255713458000000
  eta := 1333791253286548056000
  rows := #[⟨.count 2, 157978659441723120000⟩, ⟨.count 3, 18465038116565040000⟩, ⟨.count 4, 1895743913300677440⟩, ⟨.count 5, 164133672147244800⟩, ⟨.count 7, 10258354509202800⟩, ⟨.path 5, 111816216745833600⟩, ⟨.privateRow 2 26, 4570096933849847400⟩, ⟨.privateRow 2 27, 14895130747362465600⟩, ⟨.privateRow 3 23, 2261967169279217400⟩, ⟨.privateRow 3 24, 4151214124724066400⟩, ⟨.privateRow 3 25, 4862460037362127200⟩, ⟨.privateRow 4 19, 79135877642421600⟩, ⟨.privateRow 4 20, 418540863975474240⟩, ⟨.privateRow 4 21, 1223616525857709984⟩, ⟨.privateRow 4 22, 1637233379668766880⟩, ⟨.privateRow 4 23, 2031154192822154400⟩, ⟨.privateRow 4 24, 2462005082208672000⟩, ⟨.privateRow 5 16, 19756830906612800⟩, ⟨.privateRow 5 17, 81724890923315640⟩, ⟨.privateRow 5 18, 277464064820342400⟩, ⟨.privateRow 5 19, 523404043402880640⟩, ⟨.privateRow 5 20, 709057463676097536⟩, ⟨.privateRow 5 21, 865121230276102800⟩, ⟨.privateRow 5 22, 1001215400098193280⟩, ⟨.privateRow 6 10, 610616339833500⟩, ⟨.privateRow 6 13, 621718455103200⟩, ⟨.privateRow 6 14, 14532668888037300⟩, ⟨.privateRow 6 15, 61740096583165000⟩, ⟨.privateRow 6 16, 149814718978149225⟩, ⟨.privateRow 6 17, 248642973580201200⟩, ⟨.privateRow 6 18, 347074327561361400⟩, ⟨.privateRow 6 19, 423328096079768880⟩, ⟨.privateRow 6 20, 102583545092028000⟩, ⟨.privateRow 7 12, 12389960640985200⟩, ⟨.privateRow 7 13, 42205801409291520⟩, ⟨.privateRow 7 14, 88742908055802000⟩, ⟨.privateRow 7 15, 142334668815188850⟩, ⟨.privateRow 7 16, 199095819147997200⟩, ⟨.privateRow 7 17, 14166299084137200⟩, ⟨.privateRow 8 10, 10400831655163950⟩, ⟨.privateRow 8 11, 32484789279142200⟩, ⟨.privateRow 8 12, 63943743107364120⟩, ⟨.privateRow 8 13, 73328237788005200⟩, ⟨.privateRow 9 8, 10100533670599680⟩, ⟨.privateRow 9 9, 31003026961146240⟩, ⟨.privateRow 9 10, 21387114855550080⟩, ⟨.privateRow 10 6, 12749669175723480⟩, ⟨.privateRow 10 7, 8048862768759120⟩, ⟨.privateRow 11 4, 6838903006135200⟩, ⟨.hall 3 25, 366933449752254000⟩, ⟨.hall 2 26, 2858661456564513600⟩, ⟨.assumptionRow 15, 209737712532348⟩]
  caps := #[0, 0, 222026799303789480, 61105799827552480, 5202937266406880, 20274786158314688, 4883314744112077, 0, 2404760044646960, 18827409178657632, 2326283517692904, 0, 320615562982402688, 90701199416635808] }

theorem case_42_29_15_checked :
    (Witness.linear .conditional case_42_29_15).check 42 29 15 = true := by
  change case_42_29_15.check 42 29 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_29_16 : Certificate := {
  objectiveScale := 493161669000000
  eta := 2844969972746230929600
  rows := #[⟨.count 2, 337622963606882553600⟩, ⟨.count 3, 38776580044786584000⟩, ⟨.count 4, 3791487826601354880⟩, ⟨.count 5, 259878314233137600⟩, ⟨.path 5, 242559418413312000⟩, ⟨.privateRow 2 26, 13710290801549542200⟩, ⟨.privateRow 2 27, 37012143069203702400⟩, ⟨.privateRow 3 23, 5072756304800784600⟩, ⟨.privateRow 3 24, 10066865225031014400⟩, ⟨.privateRow 3 25, 12115116675368506800⟩, ⟨.privateRow 4 19, 152996030108681760⟩, ⟨.privateRow 4 20, 862727614223955480⟩, ⟨.privateRow 4 21, 2705743585347330528⟩, ⟨.privateRow 4 22, 3880735510831419240⟩, ⟨.privateRow 4 23, 5125073912797718880⟩, ⟨.privateRow 4 24, 6662801253727218600⟩, ⟨.privateRow 5 16, 44072930483982400⟩, ⟨.privateRow 5 17, 152849482187121720⟩, ⟨.privateRow 5 18, 560790046503086400⟩, ⟨.privateRow 5 19, 1141184948290427040⟩, ⟨.privateRow 5 20, 1652278966282264320⟩, ⟨.privateRow 5 21, 1591412729527661040⟩, ⟨.privateRow 5 22, 4262916207157608000⟩, ⟨.privateRow 6 13, 6994332619911000⟩, ⟨.privateRow 6 14, 27868529750000940⟩, ⟨.privateRow 6 15, 111512112905593400⟩, ⟨.privateRow 6 16, 295996270734289125⟩, ⟨.privateRow 6 17, 529037996831744400⟩, ⟨.privateRow 6 18, 791603022960149400⟩, ⟨.privateRow 6 19, 1048061885690219400⟩, ⟨.privateRow 6 20, 1020706273665678600⟩, ⟨.privateRow 7 10, 563645852154000⟩, ⟨.privateRow 7 11, 4152191110867800⟩, ⟨.privateRow 7 12, 22648315150188000⟩, ⟨.privateRow 7 13, 74153248309380240⟩, ⟨.privateRow 7 14, 170158420033602000⟩, ⟨.privateRow 7 15, 293279028022030050⟩, ⟨.privateRow 7 16, 440481181374748800⟩, ⟨.privateRow 7 17, 485073620363732400⟩, ⟨.privateRow 8 7, 113981716768920⟩, ⟨.privateRow 8 8, 366369803900100⟩, ⟨.privateRow 8 9, 4077038330580600⟩, ⟨.privateRow 8 10, 19376891850716400⟩, ⟨.privateRow 8 11, 56265520186839600⟩, ⟨.privateRow 8 12, 118654967156445720⟩, ⟨.privateRow 8 13, 202507516792781200⟩, ⟨.privateRow 8 14, 166057113617720325⟩, ⟨.privateRow 9 6, 364741493660544⟩, ⟨.privateRow 9 7, 4689533489921280⟩, ⟨.privateRow 9 8, 20201067341199360⟩, ⟨.privateRow 9 9, 32826734429448960⟩, ⟨.privateRow 9 10, 149212429224768000⟩, ⟨.privateRow 10 3, 362059570913040⟩, ⟨.privateRow 10 4, 769376588190210⟩, ⟨.privateRow 10 5, 7386015246626016⟩, ⟨.privateRow 10 6, 27697557174847560⟩, ⟨.privateRow 10 7, 37877001264748800⟩, ⟨.privateRow 11 2, 1206865236376800⟩, ⟨.privateRow 11 3, 16669826077454550⟩, ⟨.privateRow 11 4, 6838903006135200⟩, ⟨.privateRow 12 0, 6268994422290600⟩, ⟨.hall 3 25, 1373041295847144000⟩, ⟨.hall 2 26, 7531151965978440800⟩, ⟨.assumptionRow 16, 211602886495000⟩]
  caps := #[0, 0, 70525514625766200, 0, 24329141646041232, 0, 1411264309455000, 4409140482335540, 0, 67035353230907712, 0, 4089932189943600, 233090871940927000, 528278432882200000] }

theorem case_42_29_16_checked :
    (Witness.linear .conditional case_42_29_16).check 42 29 16 = true := by
  change case_42_29_16.check 42 29 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_29_17 : Certificate := {
  objectiveScale := 1593291546000000
  eta := 11902563569937824784000
  rows := #[⟨.count 2, 1431963705939618852000⟩, ⟨.count 3, 163723337966876688000⟩, ⟨.count 4, 15756832526135500800⟩, ⟨.count 5, 1025835450920280000⟩, ⟨.path 5, 1029269653323912000⟩, ⟨.privateRow 4 19, 514383204675740400⟩, ⟨.privateRow 4 22, 39253593529464514200⟩, ⟨.privateRow 4 23, 4636776238159665600⟩, ⟨.privateRow 4 24, 16372333796687668800⟩, ⟨.privateRow 5 17, 894186568052177400⟩, ⟨.privateRow 5 20, 10326743539264152000⟩, ⟨.privateRow 6 12, 2137157189417250⟩, ⟨.privateRow 6 13, 10880072964306000⟩, ⟨.privateRow 6 14, 41033418036811200⟩, ⟨.privateRow 6 15, 574657822043305000⟩, ⟨.privateRow 6 16, 325916471386130625⟩, ⟨.privateRow 6 20, 22756449752914878000⟩, ⟨.privateRow 7 10, 3381875112924000⟩, ⟨.privateRow 7 11, 4884930718668000⟩, ⟨.privateRow 7 12, 30641838144372000⟩, ⟨.privateRow 7 13, 335594740372491600⟩, ⟨.privateRow 7 14, 248317311532290000⟩, ⟨.privateRow 8 9, 1972760482539000⟩, ⟨.privateRow 8 10, 3561928649028750⟩, ⟨.privateRow 8 11, 268893231832134000⟩, ⟨.hall 8 6, 88725263827200⟩, ⟨.hall 9 6, 189763678614510⟩, ⟨.hall 8 7, 93749667971960⟩, ⟨.hall 7 8, 92124260246200⟩, ⟨.hall 10 8, 50218189098000⟩, ⟨.hall 11 8, 25787718726000⟩, ⟨.hall 6 10, 55246916322000⟩, ⟨.hall 4 17, 140235213088152⟩, ⟨.hall 3 20, 1033722037152000⟩, ⟨.hall 5 23, 1179710768558322000⟩, ⟨.hall 2 24, 609281960467956160⟩]
  caps := #[0, 194377216649616000, 709939427249052000, 0, 10433646807091200, 46256256611278560, 493673511035250, 19385704232067600, 3597966677482800, 0, 41479433450254800, 0, 2336494779899280000, 4059706859208000000] }

theorem case_42_29_17_checked :
    (Witness.linear .negative case_42_29_17).check 42 29 17 = true := by
  change case_42_29_17.check 42 29 17 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_29_18 : Certificate := {
  objectiveScale := 998
  eta := 1085546
  rows := #[⟨.assumptionRow 18, 399⟩]
  caps := #[0, 0, 555351, 233682, 135388, 63620, 32081, 18122, 7576, 8398, 6710002, 6619392, 4588844, 2616068] }

theorem case_42_29_18_checked :
    (Witness.linear .conditional case_42_29_18).check 42 29 18 = true := by
  change case_42_29_18.check 42 29 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_30_1_checked :
    (Witness.rising).check 42 30 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_30_2_checked :
    (Witness.rising).check 42 30 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_30_3_checked :
    (Witness.rising).check 42 30 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_30_4_checked :
    (Witness.rising).check 42 30 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_30_5_checked :
    (Witness.rising).check 42 30 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_30_6_checked :
    (Witness.rising).check 42 30 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_30_7_checked :
    (Witness.rising).check 42 30 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_30_8_checked :
    (Witness.rising).check 42 30 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_30_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_42_30_9_checked :
    (Witness.linear .positive case_42_30_9).check 42 30 9 = true := by
  change case_42_30_9.check 42 30 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_30_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_42_30_10_checked :
    (Witness.linear .positive case_42_30_10).check 42 30 10 = true := by
  change case_42_30_10.check 42 30 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_30_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_42_30_11_checked :
    (Witness.linear .positive case_42_30_11).check 42 30 11 = true := by
  change case_42_30_11.check 42 30 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_30_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_42_30_12_checked :
    (Witness.linear .positive case_42_30_12).check 42 30 12 = true := by
  change case_42_30_12.check 42 30 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_30_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_42_30_13_checked :
    (Witness.linear .positive case_42_30_13).check 42 30 13 = true := by
  change case_42_30_13.check 42 30 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_30_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_42_30_14_checked :
    (Witness.linear .positive case_42_30_14).check 42 30 14 = true := by
  change case_42_30_14.check 42 30 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_30_15 : Certificate := {
  objectiveScale := 164
  eta := 29745716
  rows := #[⟨.assumptionRow 15, 255⟩]
  caps := #[0, 0, 8918030, 2761650, 868530, 278200, 91091, 30635, 10659, 1522299, 1095939, 530043, 198951] }

theorem case_42_30_15_checked :
    (Witness.linear .conditional case_42_30_15).check 42 30 15 = true := by
  change case_42_30_15.check 42 30 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_30_16 : Certificate := {
  objectiveScale := 67777589880000
  eta := 815520671556523732800
  rows := #[⟨.count 2, 72265149528161990400⟩, ⟨.count 3, 5474266343855749440⟩, ⟨.count 4, 273914725078874880⟩, ⟨.count 5, 5035197152185200⟩, ⟨.path 3, 704387745116415360⟩, ⟨.path 4, 260594174634393600⟩, ⟨.privateRow 2 27, 6434981960492685600⟩, ⟨.privateRow 2 28, 8428920032758024800⟩, ⟨.privateRow 3 23, 764947151359975584⟩, ⟨.privateRow 3 24, 1383672177420492960⟩, ⟨.privateRow 3 25, 2807625932058467520⟩, ⟨.privateRow 3 26, 2646499623188541120⟩, ⟨.privateRow 4 19, 41036856790309380⟩, ⟨.privateRow 4 20, 204572867154495840⟩, ⟨.privateRow 4 21, 330980292803640480⟩, ⟨.privateRow 4 22, 750042967789507392⟩, ⟨.privateRow 4 23, 999990154423980720⟩, ⟨.privateRow 4 24, 1179578852851919520⟩, ⟨.privateRow 4 25, 1128891201519921840⟩, ⟨.privateRow 5 16, 14803479627424488⟩, ⟨.privateRow 5 17, 45428667639715360⟩, ⟨.privateRow 5 18, 88241830092045630⟩, ⟨.privateRow 5 19, 202414925517845040⟩, ⟨.privateRow 5 20, 329805413468130600⟩, ⟨.privateRow 5 21, 439874823214899072⟩, ⟨.privateRow 5 22, 525926342545744140⟩, ⟨.privateRow 5 23, 239675384444015520⟩, ⟨.privateRow 6 13, 3956226333859800⟩, ⟨.privateRow 6 14, 11770590745368000⟩, ⟨.privateRow 6 15, 23809289391047160⟩, ⟨.privateRow 6 16, 62180688641271200⟩, ⟨.privateRow 6 17, 112302879340702050⟩, ⟨.privateRow 6 18, 170271871044303600⟩, ⟨.privateRow 6 19, 230180441242752000⟩, ⟨.privateRow 6 20, 114658632294045840⟩, ⟨.privateRow 7 10, 1181729943880200⟩, ⟨.privateRow 7 11, 3873228578604000⟩, ⟨.privateRow 7 12, 8092281137440500⟩, ⟨.privateRow 7 13, 21056279000047200⟩, ⟨.privateRow 7 14, 45244842981778440⟩, ⟨.privateRow 7 15, 75128338461176000⟩, ⟨.privateRow 7 16, 110324766173772150⟩, ⟨.privateRow 7 17, 7604175291055200⟩, ⟨.privateRow 8 7, 440579750816205⟩, ⟨.privateRow 8 8, 1678399050728400⟩, ⟨.privateRow 8 9, 3812363558083080⟩, ⟨.privateRow 8 10, 9683071446510000⟩, ⟨.privateRow 8 11, 21399587896787100⟩, ⟨.privateRow 8 12, 41654812804441200⟩, ⟨.privateRow 8 13, 21349235925265248⟩, ⟨.privateRow 9 4, 111893270048560⟩, ⟨.privateRow 9 5, 1303227498212640⟩, ⟨.privateRow 9 6, 2391718647287970⟩, ⟨.privateRow 9 7, 671359620291360⟩, ⟨.privateRow 9 8, 26470750742916480⟩, ⟨.privateRow 9 9, 4183086864892320⟩, ⟨.privateRow 10 2, 636024903433920⟩, ⟨.privateRow 10 3, 3021118291311120⟩, ⟨.privateRow 10 4, 6397662263952960⟩, ⟨.privateRow 10 5, 1510559145655560⟩, ⟨.privateRow 11 0, 3021118291311120⟩, ⟨.hall 2 27, 1165288483791432000⟩, ⟨.assumptionRow 16, 37542528400608⟩]
  caps := #[0, 0, 0, 3676006299163968, 2871204969188556, 0, 270105165725472, 0, 8654684607046023, 0, 0, 125359232162671584, 289073531328075648] }

theorem case_42_30_16_checked :
    (Witness.linear .conditional case_42_30_16).check 42 30 16 = true := by
  change case_42_30_16.check 42 30 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_30_17 : Certificate := {
  objectiveScale := 4394247077220000
  eta := 85018971591635057776800
  rows := #[⟨.count 2, 7407771979900561869600⟩, ⟨.count 3, 542949337077851864160⟩, ⟨.count 4, 26115889229333904000⟩, ⟨.path 3, 86004738715653838080⟩, ⟨.path 4, 25342783483194777600⟩, ⟨.path 5, 52509913158502800⟩, ⟨.privateRow 2 27, 702190971653715343800⟩, ⟨.privateRow 3 23, 75448803983545648656⟩, ⟨.privateRow 3 25, 584604180398639441040⟩, ⟨.privateRow 3 26, 170406177221403723600⟩, ⟨.privateRow 4 20, 29007291251153014800⟩, ⟨.privateRow 4 21, 27378157208751709360⟩, ⟨.privateRow 4 22, 44161968686803631664⟩, ⟨.privateRow 4 23, 137793960546273010980⟩, ⟨.privateRow 4 24, 166488793837003638000⟩, ⟨.privateRow 4 25, 137761315684736343600⟩, ⟨.privateRow 5 14, 38085671792778610⟩, ⟨.privateRow 5 15, 148385734257579000⟩, ⟨.privateRow 5 16, 502730867664677652⟩, ⟨.privateRow 5 17, 5027308676646776520⟩, ⟨.privateRow 5 19, 38856712331930372880⟩, ⟨.privateRow 5 20, 14222278009474755220⟩, ⟨.privateRow 5 21, 45807269708251667616⟩, ⟨.privateRow 5 22, 66742419411716458410⟩, ⟨.privateRow 5 23, 87836440774659697120⟩, ⟨.privateRow 6 11, 19986649920408600⟩, ⟨.privateRow 6 12, 71746948432236000⟩, ⟨.privateRow 6 13, 198200945044051950⟩, ⟨.privateRow 6 14, 992064623322099600⟩, ⟨.privateRow 6 15, 2555626303156246320⟩, ⟨.privateRow 6 16, 1025981362580974800⟩, ⟨.privateRow 6 19, 92144007980283759500⟩, ⟨.privateRow 6 22, 28292213331778396000⟩, ⟨.privateRow 7 9, 3109034432063560⟩, ⟨.privateRow 7 11, 118382464913189400⟩, ⟨.privateRow 7 12, 73839567761509550⟩, ⟨.privateRow 7 15, 497445509130169600⟩, ⟨.privateRow 8 8, 8705296409777968⟩, ⟨.hall 9 4, 1439973842218912⟩, ⟨.hall 8 6, 1025552590593440⟩, ⟨.hall 7 7, 631439989096280⟩, ⟨.hall 9 7, 222348902107332⟩, ⟨.hall 10 7, 202135365552120⟩, ⟨.hall 7 8, 38749269680940⟩, ⟨.hall 6 9, 28534071930000⟩, ⟨.hall 6 10, 196813761137175⟩, ⟨.hall 3 26, 14929583342769215120⟩, ⟨.hall 2 27, 124516829004145578000⟩]
  caps := #[0, 0, 1148636861422890840, 0, 650290939861534972, 52509913158502800, 0, 26154377522003115, 197193888238883536, 87254486931921036, 2108736397399632000, 0, 43924893783891120000] }

theorem case_42_30_17_checked :
    (Witness.linear .negative case_42_30_17).check 42 30 17 = true := by
  change case_42_30_17.check 42 30 17 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_30_18 : Certificate := {
  objectiveScale := 622
  eta := 623770
  rows := #[⟨.assumptionRow 18, 245⟩]
  caps := #[0, 0, 306945, 137394, 78132, 35020, 18991, 10530, 4560, 14407092, 14247530, 9972948, 5798700] }

theorem case_42_30_18_checked :
    (Witness.linear .conditional case_42_30_18).check 42 30 18 = true := by
  change case_42_30_18.check 42 30 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_30_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16796, 16796, 11934] }

theorem case_42_30_19_checked :
    (Witness.linear .negative case_42_30_19).check 42 30 19 = true := by
  change case_42_30_19.check 42 30 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_31_1_checked :
    (Witness.rising).check 42 31 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_31_2_checked :
    (Witness.rising).check 42 31 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_31_3_checked :
    (Witness.rising).check 42 31 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_31_4_checked :
    (Witness.rising).check 42 31 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_31_5_checked :
    (Witness.rising).check 42 31 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_31_6_checked :
    (Witness.rising).check 42 31 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_31_7_checked :
    (Witness.rising).check 42 31 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_31_8_checked :
    (Witness.rising).check 42 31 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_31_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_42_31_9_checked :
    (Witness.linear .positive case_42_31_9).check 42 31 9 = true := by
  change case_42_31_9.check 42 31 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_31_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_42_31_10_checked :
    (Witness.linear .positive case_42_31_10).check 42 31 10 = true := by
  change case_42_31_10.check 42 31 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_31_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_42_31_11_checked :
    (Witness.linear .positive case_42_31_11).check 42 31 11 = true := by
  change case_42_31_11.check 42 31 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_31_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_42_31_12_checked :
    (Witness.linear .positive case_42_31_12).check 42 31 12 = true := by
  change case_42_31_12.check 42 31 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_31_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_42_31_13_checked :
    (Witness.linear .positive case_42_31_13).check 42 31 13 = true := by
  change case_42_31_13.check 42 31 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_31_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_42_31_14_checked :
    (Witness.linear .positive case_42_31_14).check 42 31 14 = true := by
  change case_42_31_14.check 42 31 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_31_15 : Certificate := {
  objectiveScale := 13
  eta := 9152528
  rows := #[⟨.assumptionRow 15, 33⟩]
  caps := #[0, 0, 2615008, 764218, 226746, 68510, 21164, 6721, 2211, 762, 280, 16302] }

theorem case_42_31_15_checked :
    (Witness.linear .conditional case_42_31_15).check 42 31 15 = true := by
  change case_42_31_15.check 42 31 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_31_16 : Certificate := {
  objectiveScale := 21
  eta := 4331107
  rows := #[⟨.assumptionRow 16, 25⟩]
  caps := #[0, 0, 1307504, 429590, 141474, 46852, 15652, 5291, 735471, 735471, 454461, 221901] }

theorem case_42_31_16_checked :
    (Witness.linear .conditional case_42_31_16).check 42 31 16 = true := by
  change case_42_31_16.check 42 31 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_31_17 : Certificate := {
  objectiveScale := 983
  eta := 77166771
  rows := #[⟨.assumptionRow 17, 804⟩]
  caps := #[0, 0, 25677531, 9155112, 3457392, 1231888, 422422, 178633, 58510804, 54652246, 35866566, 19403256] }

theorem case_42_31_17_checked :
    (Witness.linear .conditional case_42_31_17).check 42 31 17 = true := by
  change case_42_31_17.check 42 31 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_31_18 : Certificate := {
  objectiveScale := 24
  eta := 74613
  rows := #[⟨.assumptionRow 18, 11⟩]
  caps := #[0, 0, 28329, 15504, 6732, 3300, 1610, 728, 1396652, 1627274, 1211250, 736440] }

theorem case_42_31_18_checked :
    (Witness.linear .conditional case_42_31_18).check 42 31 18 = true := by
  change case_42_31_18.check 42 31 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_31_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 58786, 58786, 41990] }

theorem case_42_31_19_checked :
    (Witness.linear .negative case_42_31_19).check 42 31 19 = true := by
  change case_42_31_19.check 42 31 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_31_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16796] }

theorem case_42_31_20_checked :
    (Witness.linear .negative case_42_31_20).check 42 31 20 = true := by
  change case_42_31_20.check 42 31 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_32_1_checked :
    (Witness.rising).check 42 32 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_32_2_checked :
    (Witness.rising).check 42 32 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_32_3_checked :
    (Witness.rising).check 42 32 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_32_4_checked :
    (Witness.rising).check 42 32 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_32_5_checked :
    (Witness.rising).check 42 32 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_32_6_checked :
    (Witness.rising).check 42 32 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_32_7_checked :
    (Witness.rising).check 42 32 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_32_8_checked :
    (Witness.rising).check 42 32 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_32_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_42_32_9_checked :
    (Witness.linear .positive case_42_32_9).check 42 32 9 = true := by
  change case_42_32_9.check 42 32 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_32_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_42_32_10_checked :
    (Witness.linear .positive case_42_32_10).check 42 32 10 = true := by
  change case_42_32_10.check 42 32 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_32_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_42_32_11_checked :
    (Witness.linear .positive case_42_32_11).check 42 32 11 = true := by
  change case_42_32_11.check 42 32 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_32_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_42_32_12_checked :
    (Witness.linear .positive case_42_32_12).check 42 32 12 = true := by
  change case_42_32_12.check 42 32 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_32_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_42_32_13_checked :
    (Witness.linear .positive case_42_32_13).check 42 32 13 = true := by
  change case_42_32_13.check 42 32 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_32_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_42_32_14_checked :
    (Witness.linear .positive case_42_32_14).check 42 32 14 = true := by
  change case_42_32_14.check 42 32 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_32_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_42_32_15_checked :
    (Witness.linear .positive case_42_32_15).check 42 32 15 = true := by
  change case_42_32_15.check 42 32 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_32_16 : Certificate := {
  objectiveScale := 975
  eta := 506992105
  rows := #[⟨.assumptionRow 16, 1432⟩]
  caps := #[0, 0, 149382332, 44480330, 13403208, 4160988, 1365624, 457457, 158631, 32519355, 24397197] }

theorem case_42_32_16_checked :
    (Witness.linear .conditional case_42_32_16).check 42 32 16 = true := by
  change case_42_32_16.check 42 32 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_32_17 : Certificate := {
  objectiveScale := 556
  eta := 126159715
  rows := #[⟨.assumptionRow 17, 539⟩]
  caps := #[0, 0, 39878872, 12783694, 4563990, 1589364, 545272, 185725, 55160325, 49603433, 31262847] }

theorem case_42_32_17_checked :
    (Witness.linear .conditional case_42_32_17).check 42 32 17 = true := by
  change case_42_32_17.check 42 32 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_32_18 : Certificate := {
  objectiveScale := 997
  eta := 31702165
  rows := #[⟨.assumptionRow 18, 623⟩]
  caps := #[0, 0, 11630850, 4822713, 1930248, 736032, 331184, 148580, 125995840, 122251624, 84149252] }

theorem case_42_32_18_checked :
    (Witness.linear .conditional case_42_32_18).check 42 32 18 = true := by
  change case_42_32_18.check 42 32 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_32_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 208012, 208012, 149226] }

theorem case_42_32_19_checked :
    (Witness.linear .negative case_42_32_19).check 42 32 19 = true := by
  change case_42_32_19.check 42 32 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_32_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58786] }

theorem case_42_32_20_checked :
    (Witness.linear .negative case_42_32_20).check 42 32 20 = true := by
  change case_42_32_20.check 42 32 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_33_1_checked :
    (Witness.rising).check 42 33 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_33_2_checked :
    (Witness.rising).check 42 33 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_33_3_checked :
    (Witness.rising).check 42 33 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_33_4_checked :
    (Witness.rising).check 42 33 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_33_5_checked :
    (Witness.rising).check 42 33 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_33_6_checked :
    (Witness.rising).check 42 33 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_33_7_checked :
    (Witness.rising).check 42 33 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_33_8_checked :
    (Witness.rising).check 42 33 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_33_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_42_33_9_checked :
    (Witness.linear .positive case_42_33_9).check 42 33 9 = true := by
  change case_42_33_9.check 42 33 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_33_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_42_33_10_checked :
    (Witness.linear .positive case_42_33_10).check 42 33 10 = true := by
  change case_42_33_10.check 42 33 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_33_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_42_33_11_checked :
    (Witness.linear .positive case_42_33_11).check 42 33 11 = true := by
  change case_42_33_11.check 42 33 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_33_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_42_33_12_checked :
    (Witness.linear .positive case_42_33_12).check 42 33 12 = true := by
  change case_42_33_12.check 42 33 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_33_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_42_33_13_checked :
    (Witness.linear .positive case_42_33_13).check 42 33 13 = true := by
  change case_42_33_13.check 42 33 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_33_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_42_33_14_checked :
    (Witness.linear .positive case_42_33_14).check 42 33 14 = true := by
  change case_42_33_14.check 42 33 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_33_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_42_33_15_checked :
    (Witness.linear .positive case_42_33_15).check 42 33 15 = true := by
  change case_42_33_15.check 42 33 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_33_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_42_33_16_checked :
    (Witness.linear .positive case_42_33_16).check 42 33 16 = true := by
  change case_42_33_16.check 42 33 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_33_17 : Certificate := {
  objectiveScale := 936
  eta := 446895865
  rows := #[⟨.assumptionRow 17, 1033⟩]
  caps := #[0, 0, 139902928, 43836914, 13769490, 4341324, 1513408, 539695, 154208560, 133206777] }

theorem case_42_33_17_checked :
    (Witness.linear .conditional case_42_33_17).check 42 33 17 = true := by
  change case_42_33_17.check 42 33 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_33_18 : Certificate := {
  objectiveScale := 993
  eta := 27875793
  rows := #[⟨.assumptionRow 18, 611⟩]
  caps := #[0, 0, 10672794, 4214181, 1775208, 638588, 334305, 442805545, 431364885, 299663573] }

theorem case_42_33_18_checked :
    (Witness.linear .conditional case_42_33_18).check 42 33 18 = true := by
  change case_42_33_18.check 42 33 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_33_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 742900, 742900, 534888] }

theorem case_42_33_19_checked :
    (Witness.linear .negative case_42_33_19).check 42 33 19 = true := by
  change case_42_33_19.check 42 33 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_33_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 208012] }

theorem case_42_33_20_checked :
    (Witness.linear .negative case_42_33_20).check 42 33 20 = true := by
  change case_42_33_20.check 42 33 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_33_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_42_33_21_checked :
    (Witness.linear .negative case_42_33_21).check 42 33 21 = true := by
  change case_42_33_21.check 42 33 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_34_1_checked :
    (Witness.rising).check 42 34 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_34_2_checked :
    (Witness.rising).check 42 34 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_34_3_checked :
    (Witness.rising).check 42 34 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_34_4_checked :
    (Witness.rising).check 42 34 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_34_5_checked :
    (Witness.rising).check 42 34 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_34_6_checked :
    (Witness.rising).check 42 34 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_34_7_checked :
    (Witness.rising).check 42 34 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_34_8_checked :
    (Witness.rising).check 42 34 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_34_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1] }

theorem case_42_34_9_checked :
    (Witness.linear .positive case_42_34_9).check 42 34 9 = true := by
  change case_42_34_9.check 42 34 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_34_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1] }

theorem case_42_34_10_checked :
    (Witness.linear .positive case_42_34_10).check 42 34 10 = true := by
  change case_42_34_10.check 42 34 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_34_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_42_34_11_checked :
    (Witness.linear .positive case_42_34_11).check 42 34 11 = true := by
  change case_42_34_11.check 42 34 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_34_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_42_34_12_checked :
    (Witness.linear .positive case_42_34_12).check 42 34 12 = true := by
  change case_42_34_12.check 42 34 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_34_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_42_34_13_checked :
    (Witness.linear .positive case_42_34_13).check 42 34 13 = true := by
  change case_42_34_13.check 42 34 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_34_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_42_34_14_checked :
    (Witness.linear .positive case_42_34_14).check 42 34 14 = true := by
  change case_42_34_14.check 42 34 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_34_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_42_34_15_checked :
    (Witness.linear .positive case_42_34_15).check 42 34 15 = true := by
  change case_42_34_15.check 42 34 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_34_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_42_34_16_checked :
    (Witness.linear .positive case_42_34_16).check 42 34 16 = true := by
  change case_42_34_16.check 42 34 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_34_17 : Certificate := {
  objectiveScale := 5
  eta := 11759670
  rows := #[⟨.assumptionRow 17, 8⟩]
  caps := #[0, 0, 3380195, 1010344, 305558, 93670, 29172, 9256, 3003] }

theorem case_42_34_17_checked :
    (Witness.linear .conditional case_42_34_17).check 42 34 17 = true := by
  change case_42_34_17.check 42 34 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_34_18 : Certificate := {
  objectiveScale := 529
  eta := 81238300
  rows := #[⟨.assumptionRow 18, 415⟩]
  caps := #[0, 0, 31418552, 11181291, 3782976, 1449624, 553588, 389347335, 369549050] }

theorem case_42_34_18_checked :
    (Witness.linear .conditional case_42_34_18).check 42 34 18 = true := by
  change case_42_34_18.check 42 34 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_34_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 2674440, 2674440, 1931540] }

theorem case_42_34_19_checked :
    (Witness.linear .negative case_42_34_19).check 42 34 19 = true := by
  change case_42_34_19.check 42 34 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_34_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 742900] }

theorem case_42_34_20_checked :
    (Witness.linear .negative case_42_34_20).check 42 34 20 = true := by
  change case_42_34_20.check 42 34 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_34_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_42_34_21_checked :
    (Witness.linear .negative case_42_34_21).check 42 34 21 = true := by
  change case_42_34_21.check 42 34 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_34_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_42_34_22_checked :
    (Witness.linear .negative case_42_34_22).check 42 34 22 = true := by
  change case_42_34_22.check 42 34 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_35_1_checked :
    (Witness.rising).check 42 35 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_35_2_checked :
    (Witness.rising).check 42 35 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_35_3_checked :
    (Witness.rising).check 42 35 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_35_4_checked :
    (Witness.rising).check 42 35 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_35_5_checked :
    (Witness.rising).check 42 35 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_35_6_checked :
    (Witness.rising).check 42 35 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_35_7_checked :
    (Witness.rising).check 42 35 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_35_8_checked :
    (Witness.rising).check 42 35 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_35_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1] }

theorem case_42_35_9_checked :
    (Witness.linear .positive case_42_35_9).check 42 35 9 = true := by
  change case_42_35_9.check 42 35 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_35_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2] }

theorem case_42_35_10_checked :
    (Witness.linear .positive case_42_35_10).check 42 35 10 = true := by
  change case_42_35_10.check 42 35 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_35_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5] }

theorem case_42_35_11_checked :
    (Witness.linear .positive case_42_35_11).check 42 35 11 = true := by
  change case_42_35_11.check 42 35 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_35_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14] }

theorem case_42_35_12_checked :
    (Witness.linear .positive case_42_35_12).check 42 35 12 = true := by
  change case_42_35_12.check 42 35 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_35_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42] }

theorem case_42_35_13_checked :
    (Witness.linear .positive case_42_35_13).check 42 35 13 = true := by
  change case_42_35_13.check 42 35 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_35_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_42_35_14_checked :
    (Witness.linear .positive case_42_35_14).check 42 35 14 = true := by
  change case_42_35_14.check 42 35 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_35_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_42_35_15_checked :
    (Witness.linear .positive case_42_35_15).check 42 35 15 = true := by
  change case_42_35_15.check 42 35 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_35_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_42_35_16_checked :
    (Witness.linear .positive case_42_35_16).check 42 35 16 = true := by
  change case_42_35_16.check 42 35 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_35_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_42_35_17_checked :
    (Witness.linear .positive case_42_35_17).check 42 35 17 = true := by
  change case_42_35_17.check 42 35 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_35_18 : Certificate := {
  objectiveScale := 597
  eta := 297059490
  rows := #[⟨.assumptionRow 18, 551⟩]
  caps := #[0, 0, 101451735, 33749947, 11029158, 3558168, 1338648, 740262705] }

theorem case_42_35_18_checked :
    (Witness.linear .conditional case_42_35_18).check 42 35 18 = true := by
  change case_42_35_18.check 42 35 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_35_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 9694845, 9694845, 7020405] }

theorem case_42_35_19_checked :
    (Witness.linear .negative case_42_35_19).check 42 35 19 = true := by
  change case_42_35_19.check 42 35 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_35_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 2674440] }

theorem case_42_35_20_checked :
    (Witness.linear .negative case_42_35_20).check 42 35 20 = true := by
  change case_42_35_20.check 42 35 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_35_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_42_35_21_checked :
    (Witness.linear .negative case_42_35_21).check 42 35 21 = true := by
  change case_42_35_21.check 42 35 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_35_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_42_35_22_checked :
    (Witness.linear .negative case_42_35_22).check 42 35 22 = true := by
  change case_42_35_22.check 42 35 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_36_1_checked :
    (Witness.rising).check 42 36 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_36_2_checked :
    (Witness.rising).check 42 36 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_36_3_checked :
    (Witness.rising).check 42 36 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_36_4_checked :
    (Witness.rising).check 42 36 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_36_5_checked :
    (Witness.rising).check 42 36 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_36_6_checked :
    (Witness.rising).check 42 36 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_36_7_checked :
    (Witness.rising).check 42 36 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_36_8_checked :
    (Witness.rising).check 42 36 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_36_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2] }

theorem case_42_36_9_checked :
    (Witness.linear .positive case_42_36_9).check 42 36 9 = true := by
  change case_42_36_9.check 42 36 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_36_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_42_36_10_checked :
    (Witness.linear .positive case_42_36_10).check 42 36 10 = true := by
  change case_42_36_10.check 42 36 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_36_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14] }

theorem case_42_36_11_checked :
    (Witness.linear .positive case_42_36_11).check 42 36 11 = true := by
  change case_42_36_11.check 42 36 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_36_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42] }

theorem case_42_36_12_checked :
    (Witness.linear .positive case_42_36_12).check 42 36 12 = true := by
  change case_42_36_12.check 42 36 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_36_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132] }

theorem case_42_36_13_checked :
    (Witness.linear .positive case_42_36_13).check 42 36 13 = true := by
  change case_42_36_13.check 42 36 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_36_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429] }

theorem case_42_36_14_checked :
    (Witness.linear .positive case_42_36_14).check 42 36 14 = true := by
  change case_42_36_14.check 42 36 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_36_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430] }

theorem case_42_36_15_checked :
    (Witness.linear .positive case_42_36_15).check 42 36 15 = true := by
  change case_42_36_15.check 42 36 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_36_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862] }

theorem case_42_36_16_checked :
    (Witness.linear .positive case_42_36_16).check 42 36 16 = true := by
  change case_42_36_16.check 42 36 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_36_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796] }

theorem case_42_36_17_checked :
    (Witness.linear .positive case_42_36_17).check 42 36 17 = true := by
  change case_42_36_17.check 42 36 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_36_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_42_36_18_checked :
    (Witness.linear .positive case_42_36_18).check 42 36 18 = true := by
  change case_42_36_18.check 42 36 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_36_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 35357670, 35357670, 25662825] }

theorem case_42_36_19_checked :
    (Witness.linear .negative case_42_36_19).check 42 36 19 = true := by
  change case_42_36_19.check 42 36 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_36_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 9694845] }

theorem case_42_36_20_checked :
    (Witness.linear .negative case_42_36_20).check 42 36 20 = true := by
  change case_42_36_20.check 42 36 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_36_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_42_36_21_checked :
    (Witness.linear .negative case_42_36_21).check 42 36 21 = true := by
  change case_42_36_21.check 42 36 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_36_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_42_36_22_checked :
    (Witness.linear .negative case_42_36_22).check 42 36 22 = true := by
  change case_42_36_22.check 42 36 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_36_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_42_36_23_checked :
    (Witness.linear .negative case_42_36_23).check 42 36 23 = true := by
  change case_42_36_23.check 42 36 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_37_1_checked :
    (Witness.rising).check 42 37 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_37_2_checked :
    (Witness.rising).check 42 37 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_37_3_checked :
    (Witness.rising).check 42 37 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_37_4_checked :
    (Witness.rising).check 42 37 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_37_5_checked :
    (Witness.rising).check 42 37 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_37_6_checked :
    (Witness.rising).check 42 37 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_37_7_checked :
    (Witness.rising).check 42 37 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_37_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2] }

theorem case_42_37_8_checked :
    (Witness.linear .positive case_42_37_8).check 42 37 8 = true := by
  change case_42_37_8.check 42 37 8 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_37_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5] }

theorem case_42_37_9_checked :
    (Witness.linear .positive case_42_37_9).check 42 37 9 = true := by
  change case_42_37_9.check 42 37 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_37_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_42_37_10_checked :
    (Witness.linear .positive case_42_37_10).check 42 37 10 = true := by
  change case_42_37_10.check 42 37 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_37_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_42_37_11_checked :
    (Witness.linear .positive case_42_37_11).check 42 37 11 = true := by
  change case_42_37_11.check 42 37 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_37_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132] }

theorem case_42_37_12_checked :
    (Witness.linear .positive case_42_37_12).check 42 37 12 = true := by
  change case_42_37_12.check 42 37 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_37_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429] }

theorem case_42_37_13_checked :
    (Witness.linear .positive case_42_37_13).check 42 37 13 = true := by
  change case_42_37_13.check 42 37 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_37_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430] }

theorem case_42_37_14_checked :
    (Witness.linear .positive case_42_37_14).check 42 37 14 = true := by
  change case_42_37_14.check 42 37 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_37_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862] }

theorem case_42_37_15_checked :
    (Witness.linear .positive case_42_37_15).check 42 37 15 = true := by
  change case_42_37_15.check 42 37 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_37_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796] }

theorem case_42_37_16_checked :
    (Witness.linear .positive case_42_37_16).check 42 37 16 = true := by
  change case_42_37_16.check 42 37 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_37_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786] }

theorem case_42_37_17_checked :
    (Witness.linear .positive case_42_37_17).check 42 37 17 = true := by
  change case_42_37_17.check 42 37 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_37_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012] }

theorem case_42_37_18_checked :
    (Witness.linear .positive case_42_37_18).check 42 37 18 = true := by
  change case_42_37_18.check 42 37 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_37_19 : Certificate := {
  objectiveScale := 804
  eta := 307653060
  rows := #[⟨.assumptionRow 19, 611⟩]
  caps := #[0, 0, 104311900, 36461095, 14048562, 4984536] }

theorem case_42_37_19_checked :
    (Witness.linear .conditional case_42_37_19).check 42 37 19 = true := by
  change case_42_37_19.check 42 37 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_37_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 35357670] }

theorem case_42_37_20_checked :
    (Witness.linear .negative case_42_37_20).check 42 37 20 = true := by
  change case_42_37_20.check 42 37 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_37_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_42_37_21_checked :
    (Witness.linear .negative case_42_37_21).check 42 37 21 = true := by
  change case_42_37_21.check 42 37 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_37_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_42_37_22_checked :
    (Witness.linear .negative case_42_37_22).check 42 37 22 = true := by
  change case_42_37_22.check 42 37 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_37_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_42_37_23_checked :
    (Witness.linear .negative case_42_37_23).check 42 37 23 = true := by
  change case_42_37_23.check 42 37 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_37_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_42_37_24_checked :
    (Witness.linear .negative case_42_37_24).check 42 37 24 = true := by
  change case_42_37_24.check 42 37 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_38_1_checked :
    (Witness.rising).check 42 38 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_38_2_checked :
    (Witness.rising).check 42 38 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_38_3_checked :
    (Witness.rising).check 42 38 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_38_4_checked :
    (Witness.rising).check 42 38 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_38_5_checked :
    (Witness.rising).check 42 38 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_38_6_checked :
    (Witness.rising).check 42 38 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_38_7_checked :
    (Witness.rising).check 42 38 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_38_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5] }

theorem case_42_38_8_checked :
    (Witness.linear .positive case_42_38_8).check 42 38 8 = true := by
  change case_42_38_8.check 42 38 8 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_38_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14] }

theorem case_42_38_9_checked :
    (Witness.linear .positive case_42_38_9).check 42 38 9 = true := by
  change case_42_38_9.check 42 38 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_38_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_42_38_10_checked :
    (Witness.linear .positive case_42_38_10).check 42 38 10 = true := by
  change case_42_38_10.check 42 38 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_38_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_42_38_11_checked :
    (Witness.linear .positive case_42_38_11).check 42 38 11 = true := by
  change case_42_38_11.check 42 38 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_38_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429] }

theorem case_42_38_12_checked :
    (Witness.linear .positive case_42_38_12).check 42 38 12 = true := by
  change case_42_38_12.check 42 38 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_38_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430] }

theorem case_42_38_13_checked :
    (Witness.linear .positive case_42_38_13).check 42 38 13 = true := by
  change case_42_38_13.check 42 38 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_38_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862] }

theorem case_42_38_14_checked :
    (Witness.linear .positive case_42_38_14).check 42 38 14 = true := by
  change case_42_38_14.check 42 38 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_38_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796] }

theorem case_42_38_15_checked :
    (Witness.linear .positive case_42_38_15).check 42 38 15 = true := by
  change case_42_38_15.check 42 38 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_38_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786] }

theorem case_42_38_16_checked :
    (Witness.linear .positive case_42_38_16).check 42 38 16 = true := by
  change case_42_38_16.check 42 38 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_38_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012] }

theorem case_42_38_17_checked :
    (Witness.linear .positive case_42_38_17).check 42 38 17 = true := by
  change case_42_38_17.check 42 38 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_38_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900] }

theorem case_42_38_18_checked :
    (Witness.linear .positive case_42_38_18).check 42 38 18 = true := by
  change case_42_38_18.check 42 38 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_38_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440] }

theorem case_42_38_19_checked :
    (Witness.linear .positive case_42_38_19).check 42 38 19 = true := by
  change case_42_38_19.check 42 38 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_38_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 129644790] }

theorem case_42_38_20_checked :
    (Witness.linear .negative case_42_38_20).check 42 38 20 = true := by
  change case_42_38_20.check 42 38 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_38_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_42_38_21_checked :
    (Witness.linear .negative case_42_38_21).check 42 38 21 = true := by
  change case_42_38_21.check 42 38 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_38_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_42_38_22_checked :
    (Witness.linear .negative case_42_38_22).check 42 38 22 = true := by
  change case_42_38_22.check 42 38 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_38_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_42_38_23_checked :
    (Witness.linear .negative case_42_38_23).check 42 38 23 = true := by
  change case_42_38_23.check 42 38 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_38_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_42_38_24_checked :
    (Witness.linear .negative case_42_38_24).check 42 38 24 = true := by
  change case_42_38_24.check 42 38 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_39_1_checked :
    (Witness.rising).check 42 39 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_39_2_checked :
    (Witness.rising).check 42 39 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_39_3_checked :
    (Witness.rising).check 42 39 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_39_4_checked :
    (Witness.rising).check 42 39 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_39_5_checked :
    (Witness.rising).check 42 39 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_39_6_checked :
    (Witness.rising).check 42 39 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_39_7_checked :
    (Witness.rising).check 42 39 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_39_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14] }

theorem case_42_39_8_checked :
    (Witness.linear .positive case_42_39_8).check 42 39 8 = true := by
  change case_42_39_8.check 42 39 8 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_39_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_42_39_9_checked :
    (Witness.linear .positive case_42_39_9).check 42 39 9 = true := by
  change case_42_39_9.check 42 39 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_39_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_42_39_10_checked :
    (Witness.linear .positive case_42_39_10).check 42 39 10 = true := by
  change case_42_39_10.check 42 39 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_39_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_42_39_11_checked :
    (Witness.linear .positive case_42_39_11).check 42 39 11 = true := by
  change case_42_39_11.check 42 39 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_39_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_42_39_12_checked :
    (Witness.linear .positive case_42_39_12).check 42 39 12 = true := by
  change case_42_39_12.check 42 39 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_39_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862] }

theorem case_42_39_13_checked :
    (Witness.linear .positive case_42_39_13).check 42 39 13 = true := by
  change case_42_39_13.check 42 39 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_39_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796] }

theorem case_42_39_14_checked :
    (Witness.linear .positive case_42_39_14).check 42 39 14 = true := by
  change case_42_39_14.check 42 39 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_39_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786] }

theorem case_42_39_15_checked :
    (Witness.linear .positive case_42_39_15).check 42 39 15 = true := by
  change case_42_39_15.check 42 39 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_39_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012] }

theorem case_42_39_16_checked :
    (Witness.linear .positive case_42_39_16).check 42 39 16 = true := by
  change case_42_39_16.check 42 39 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_39_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900] }

theorem case_42_39_17_checked :
    (Witness.linear .positive case_42_39_17).check 42 39 17 = true := by
  change case_42_39_17.check 42 39 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_39_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440] }

theorem case_42_39_18_checked :
    (Witness.linear .positive case_42_39_18).check 42 39 18 = true := by
  change case_42_39_18.check 42 39 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_39_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845] }

theorem case_42_39_19_checked :
    (Witness.linear .positive case_42_39_19).check 42 39 19 = true := by
  change case_42_39_19.check 42 39 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_39_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 477638700] }

theorem case_42_39_20_checked :
    (Witness.linear .negative case_42_39_20).check 42 39 20 = true := by
  change case_42_39_20.check 42 39 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_39_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_42_39_21_checked :
    (Witness.linear .negative case_42_39_21).check 42 39 21 = true := by
  change case_42_39_21.check 42 39 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_39_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_42_39_22_checked :
    (Witness.linear .negative case_42_39_22).check 42 39 22 = true := by
  change case_42_39_22.check 42 39 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_39_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_42_39_23_checked :
    (Witness.linear .negative case_42_39_23).check 42 39 23 = true := by
  change case_42_39_23.check 42 39 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_39_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_42_39_24_checked :
    (Witness.linear .negative case_42_39_24).check 42 39 24 = true := by
  change case_42_39_24.check 42 39 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_39_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_42_39_25_checked :
    (Witness.linear .negative case_42_39_25).check 42 39 25 = true := by
  change case_42_39_25.check 42 39 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_40_1_checked :
    (Witness.rising).check 42 40 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_40_2_checked :
    (Witness.rising).check 42 40 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_40_3_checked :
    (Witness.rising).check 42 40 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_40_4_checked :
    (Witness.rising).check 42 40 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_40_5_checked :
    (Witness.rising).check 42 40 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_40_6_checked :
    (Witness.rising).check 42 40 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_40_7_checked :
    (Witness.rising).check 42 40 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_40_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42] }

theorem case_42_40_8_checked :
    (Witness.linear .positive case_42_40_8).check 42 40 8 = true := by
  change case_42_40_8.check 42 40 8 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_40_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_42_40_9_checked :
    (Witness.linear .positive case_42_40_9).check 42 40 9 = true := by
  change case_42_40_9.check 42 40 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_40_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_42_40_10_checked :
    (Witness.linear .positive case_42_40_10).check 42 40 10 = true := by
  change case_42_40_10.check 42 40 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_40_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_42_40_11_checked :
    (Witness.linear .positive case_42_40_11).check 42 40 11 = true := by
  change case_42_40_11.check 42 40 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_40_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_42_40_12_checked :
    (Witness.linear .positive case_42_40_12).check 42 40 12 = true := by
  change case_42_40_12.check 42 40 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_40_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796] }

theorem case_42_40_13_checked :
    (Witness.linear .positive case_42_40_13).check 42 40 13 = true := by
  change case_42_40_13.check 42 40 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_40_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786] }

theorem case_42_40_14_checked :
    (Witness.linear .positive case_42_40_14).check 42 40 14 = true := by
  change case_42_40_14.check 42 40 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_40_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012] }

theorem case_42_40_15_checked :
    (Witness.linear .positive case_42_40_15).check 42 40 15 = true := by
  change case_42_40_15.check 42 40 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_40_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900] }

theorem case_42_40_16_checked :
    (Witness.linear .positive case_42_40_16).check 42 40 16 = true := by
  change case_42_40_16.check 42 40 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_40_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440] }

theorem case_42_40_17_checked :
    (Witness.linear .positive case_42_40_17).check 42 40 17 = true := by
  change case_42_40_17.check 42 40 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_40_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845] }

theorem case_42_40_18_checked :
    (Witness.linear .positive case_42_40_18).check 42 40 18 = true := by
  change case_42_40_18.check 42 40 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_40_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670] }

theorem case_42_40_19_checked :
    (Witness.linear .positive case_42_40_19).check 42 40 19 = true := by
  change case_42_40_19.check 42 40 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_40_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790] }

theorem case_42_40_20_checked :
    (Witness.linear .positive case_42_40_20).check 42 40 20 = true := by
  change case_42_40_20.check 42 40 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_40_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_42_40_21_checked :
    (Witness.linear .negative case_42_40_21).check 42 40 21 = true := by
  change case_42_40_21.check 42 40 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_40_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_42_40_22_checked :
    (Witness.linear .negative case_42_40_22).check 42 40 22 = true := by
  change case_42_40_22.check 42 40 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_40_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_42_40_23_checked :
    (Witness.linear .negative case_42_40_23).check 42 40 23 = true := by
  change case_42_40_23.check 42 40 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_40_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_42_40_24_checked :
    (Witness.linear .negative case_42_40_24).check 42 40 24 = true := by
  change case_42_40_24.check 42 40 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_40_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_42_40_25_checked :
    (Witness.linear .negative case_42_40_25).check 42 40 25 = true := by
  change case_42_40_25.check 42 40 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_40_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_42_40_26_checked :
    (Witness.linear .negative case_42_40_26).check 42 40 26 = true := by
  change case_42_40_26.check 42 40 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_41_1_checked :
    (Witness.rising).check 42 41 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_41_2_checked :
    (Witness.rising).check 42 41 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_41_3_checked :
    (Witness.rising).check 42 41 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_41_4_checked :
    (Witness.rising).check 42 41 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_41_5_checked :
    (Witness.rising).check 42 41 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_41_6_checked :
    (Witness.rising).check 42 41 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_42_41_7_checked :
    (Witness.rising).check 42 41 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_41_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0] }

theorem case_42_41_8_checked :
    (Witness.linear .positive case_42_41_8).check 42 41 8 = true := by
  change case_42_41_8.check 42 41 8 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_41_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_42_41_9_checked :
    (Witness.linear .positive case_42_41_9).check 42 41 9 = true := by
  change case_42_41_9.check 42 41 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_41_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_42_41_10_checked :
    (Witness.linear .positive case_42_41_10).check 42 41 10 = true := by
  change case_42_41_10.check 42 41 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_41_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_42_41_11_checked :
    (Witness.linear .positive case_42_41_11).check 42 41 11 = true := by
  change case_42_41_11.check 42 41 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_41_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_42_41_12_checked :
    (Witness.linear .positive case_42_41_12).check 42 41 12 = true := by
  change case_42_41_12.check 42 41 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_41_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_42_41_13_checked :
    (Witness.linear .positive case_42_41_13).check 42 41 13 = true := by
  change case_42_41_13.check 42 41 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_41_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0] }

theorem case_42_41_14_checked :
    (Witness.linear .positive case_42_41_14).check 42 41 14 = true := by
  change case_42_41_14.check 42 41 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_41_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0] }

theorem case_42_41_15_checked :
    (Witness.linear .positive case_42_41_15).check 42 41 15 = true := by
  change case_42_41_15.check 42 41 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_41_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0] }

theorem case_42_41_16_checked :
    (Witness.linear .positive case_42_41_16).check 42 41 16 = true := by
  change case_42_41_16.check 42 41 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_41_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0] }

theorem case_42_41_17_checked :
    (Witness.linear .positive case_42_41_17).check 42 41 17 = true := by
  change case_42_41_17.check 42 41 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_41_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0] }

theorem case_42_41_18_checked :
    (Witness.linear .positive case_42_41_18).check 42 41 18 = true := by
  change case_42_41_18.check 42 41 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_41_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0] }

theorem case_42_41_19_checked :
    (Witness.linear .positive case_42_41_19).check 42 41 19 = true := by
  change case_42_41_19.check 42 41 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_41_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0] }

theorem case_42_41_20_checked :
    (Witness.linear .positive case_42_41_20).check 42 41 20 = true := by
  change case_42_41_20.check 42 41 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_41_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_42_41_21_checked :
    (Witness.linear .negative case_42_41_21).check 42 41 21 = true := by
  change case_42_41_21.check 42 41 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_41_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_42_41_22_checked :
    (Witness.linear .negative case_42_41_22).check 42 41 22 = true := by
  change case_42_41_22.check 42 41 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_41_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_42_41_23_checked :
    (Witness.linear .negative case_42_41_23).check 42 41 23 = true := by
  change case_42_41_23.check 42 41 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_41_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_42_41_24_checked :
    (Witness.linear .negative case_42_41_24).check 42 41 24 = true := by
  change case_42_41_24.check 42 41 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_41_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_42_41_25_checked :
    (Witness.linear .negative case_42_41_25).check 42 41 25 = true := by
  change case_42_41_25.check 42 41 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_42_41_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_42_41_26_checked :
    (Witness.linear .negative case_42_41_26).check 42 41 26 = true := by
  change case_42_41_26.check 42 41 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_42 (a k : ℕ) (h : Domain 42 a k) :
    ∃ w : Witness, w.check 42 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 21 ≤ a := by omega
  have haHi : a ≤ 41 := by omega
  interval_cases a

  · have hkHi : k ≤ 13 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_42_21_1_checked⟩

    · exact ⟨Witness.rising, case_42_21_2_checked⟩

    · exact ⟨Witness.rising, case_42_21_3_checked⟩

    · exact ⟨Witness.rising, case_42_21_4_checked⟩

    · exact ⟨Witness.rising, case_42_21_5_checked⟩

    · exact ⟨Witness.rising, case_42_21_6_checked⟩

    · exact ⟨Witness.rising, case_42_21_7_checked⟩

    · exact ⟨Witness.rising, case_42_21_8_checked⟩

    · exact ⟨Witness.rising, case_42_21_9_checked⟩

    · exact ⟨Witness.linear .positive case_42_21_10, case_42_21_10_checked⟩

    · exact ⟨Witness.linear .positive case_42_21_11, case_42_21_11_checked⟩

    · exact ⟨Witness.linear .conditional case_42_21_12, case_42_21_12_checked⟩

    · exact ⟨Witness.linear .conditional case_42_21_13, case_42_21_13_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_42_22_1_checked⟩

    · exact ⟨Witness.rising, case_42_22_2_checked⟩

    · exact ⟨Witness.rising, case_42_22_3_checked⟩

    · exact ⟨Witness.rising, case_42_22_4_checked⟩

    · exact ⟨Witness.rising, case_42_22_5_checked⟩

    · exact ⟨Witness.rising, case_42_22_6_checked⟩

    · exact ⟨Witness.rising, case_42_22_7_checked⟩

    · exact ⟨Witness.rising, case_42_22_8_checked⟩

    · exact ⟨Witness.linear .positive case_42_22_9, case_42_22_9_checked⟩

    · exact ⟨Witness.linear .positive case_42_22_10, case_42_22_10_checked⟩

    · exact ⟨Witness.linear .positive case_42_22_11, case_42_22_11_checked⟩

    · exact ⟨Witness.linear .positive case_42_22_12, case_42_22_12_checked⟩

    · exact ⟨Witness.linear .conditional case_42_22_13, case_42_22_13_checked⟩

    · exact ⟨Witness.linear .conditional case_42_22_14, case_42_22_14_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_42_23_1_checked⟩

    · exact ⟨Witness.rising, case_42_23_2_checked⟩

    · exact ⟨Witness.rising, case_42_23_3_checked⟩

    · exact ⟨Witness.rising, case_42_23_4_checked⟩

    · exact ⟨Witness.rising, case_42_23_5_checked⟩

    · exact ⟨Witness.rising, case_42_23_6_checked⟩

    · exact ⟨Witness.rising, case_42_23_7_checked⟩

    · exact ⟨Witness.rising, case_42_23_8_checked⟩

    · exact ⟨Witness.linear .positive case_42_23_9, case_42_23_9_checked⟩

    · exact ⟨Witness.linear .positive case_42_23_10, case_42_23_10_checked⟩

    · exact ⟨Witness.linear .positive case_42_23_11, case_42_23_11_checked⟩

    · exact ⟨Witness.linear .positive case_42_23_12, case_42_23_12_checked⟩

    · exact ⟨Witness.linear .conditional case_42_23_13, case_42_23_13_checked⟩

    · exact ⟨Witness.linear .conditional case_42_23_14, case_42_23_14_checked⟩

  · have hkHi : k ≤ 15 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_42_24_1_checked⟩

    · exact ⟨Witness.rising, case_42_24_2_checked⟩

    · exact ⟨Witness.rising, case_42_24_3_checked⟩

    · exact ⟨Witness.rising, case_42_24_4_checked⟩

    · exact ⟨Witness.rising, case_42_24_5_checked⟩

    · exact ⟨Witness.rising, case_42_24_6_checked⟩

    · exact ⟨Witness.rising, case_42_24_7_checked⟩

    · exact ⟨Witness.rising, case_42_24_8_checked⟩

    · exact ⟨Witness.linear .positive case_42_24_9, case_42_24_9_checked⟩

    · exact ⟨Witness.linear .positive case_42_24_10, case_42_24_10_checked⟩

    · exact ⟨Witness.linear .positive case_42_24_11, case_42_24_11_checked⟩

    · exact ⟨Witness.linear .positive case_42_24_12, case_42_24_12_checked⟩

    · exact ⟨Witness.linear .conditional case_42_24_13, case_42_24_13_checked⟩

    · exact ⟨Witness.linear .conditional case_42_24_14, case_42_24_14_checked⟩

    · exact ⟨Witness.linear .conditional case_42_24_15, case_42_24_15_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_42_25_1_checked⟩

    · exact ⟨Witness.rising, case_42_25_2_checked⟩

    · exact ⟨Witness.rising, case_42_25_3_checked⟩

    · exact ⟨Witness.rising, case_42_25_4_checked⟩

    · exact ⟨Witness.rising, case_42_25_5_checked⟩

    · exact ⟨Witness.rising, case_42_25_6_checked⟩

    · exact ⟨Witness.rising, case_42_25_7_checked⟩

    · exact ⟨Witness.rising, case_42_25_8_checked⟩

    · exact ⟨Witness.linear .positive case_42_25_9, case_42_25_9_checked⟩

    · exact ⟨Witness.linear .positive case_42_25_10, case_42_25_10_checked⟩

    · exact ⟨Witness.linear .positive case_42_25_11, case_42_25_11_checked⟩

    · exact ⟨Witness.linear .positive case_42_25_12, case_42_25_12_checked⟩

    · exact ⟨Witness.linear .conditional case_42_25_13, case_42_25_13_checked⟩

    · exact ⟨Witness.linear .conditional case_42_25_14, case_42_25_14_checked⟩

    · exact ⟨Witness.linear .conditional case_42_25_15, case_42_25_15_checked⟩

    · exact ⟨Witness.linear .negative case_42_25_16, case_42_25_16_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_42_26_1_checked⟩

    · exact ⟨Witness.rising, case_42_26_2_checked⟩

    · exact ⟨Witness.rising, case_42_26_3_checked⟩

    · exact ⟨Witness.rising, case_42_26_4_checked⟩

    · exact ⟨Witness.rising, case_42_26_5_checked⟩

    · exact ⟨Witness.rising, case_42_26_6_checked⟩

    · exact ⟨Witness.rising, case_42_26_7_checked⟩

    · exact ⟨Witness.rising, case_42_26_8_checked⟩

    · exact ⟨Witness.linear .positive case_42_26_9, case_42_26_9_checked⟩

    · exact ⟨Witness.linear .positive case_42_26_10, case_42_26_10_checked⟩

    · exact ⟨Witness.linear .positive case_42_26_11, case_42_26_11_checked⟩

    · exact ⟨Witness.linear .positive case_42_26_12, case_42_26_12_checked⟩

    · exact ⟨Witness.linear .conditional case_42_26_13, case_42_26_13_checked⟩

    · exact ⟨Witness.linear .conditional case_42_26_14, case_42_26_14_checked⟩

    · exact ⟨Witness.linear .conditional case_42_26_15, case_42_26_15_checked⟩

    · exact ⟨Witness.linear .negative case_42_26_16, case_42_26_16_checked⟩

  · have hkHi : k ≤ 17 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_42_27_1_checked⟩

    · exact ⟨Witness.rising, case_42_27_2_checked⟩

    · exact ⟨Witness.rising, case_42_27_3_checked⟩

    · exact ⟨Witness.rising, case_42_27_4_checked⟩

    · exact ⟨Witness.rising, case_42_27_5_checked⟩

    · exact ⟨Witness.rising, case_42_27_6_checked⟩

    · exact ⟨Witness.rising, case_42_27_7_checked⟩

    · exact ⟨Witness.rising, case_42_27_8_checked⟩

    · exact ⟨Witness.linear .positive case_42_27_9, case_42_27_9_checked⟩

    · exact ⟨Witness.linear .positive case_42_27_10, case_42_27_10_checked⟩

    · exact ⟨Witness.linear .positive case_42_27_11, case_42_27_11_checked⟩

    · exact ⟨Witness.linear .positive case_42_27_12, case_42_27_12_checked⟩

    · exact ⟨Witness.linear .positive case_42_27_13, case_42_27_13_checked⟩

    · exact ⟨Witness.linear .conditional case_42_27_14, case_42_27_14_checked⟩

    · exact ⟨Witness.linear .conditional case_42_27_15, case_42_27_15_checked⟩

    · exact ⟨Witness.linear .negative case_42_27_16, case_42_27_16_checked⟩

    · exact ⟨Witness.linear .negative case_42_27_17, case_42_27_17_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_42_28_1_checked⟩

    · exact ⟨Witness.rising, case_42_28_2_checked⟩

    · exact ⟨Witness.rising, case_42_28_3_checked⟩

    · exact ⟨Witness.rising, case_42_28_4_checked⟩

    · exact ⟨Witness.rising, case_42_28_5_checked⟩

    · exact ⟨Witness.rising, case_42_28_6_checked⟩

    · exact ⟨Witness.rising, case_42_28_7_checked⟩

    · exact ⟨Witness.rising, case_42_28_8_checked⟩

    · exact ⟨Witness.linear .positive case_42_28_9, case_42_28_9_checked⟩

    · exact ⟨Witness.linear .positive case_42_28_10, case_42_28_10_checked⟩

    · exact ⟨Witness.linear .positive case_42_28_11, case_42_28_11_checked⟩

    · exact ⟨Witness.linear .positive case_42_28_12, case_42_28_12_checked⟩

    · exact ⟨Witness.linear .positive case_42_28_13, case_42_28_13_checked⟩

    · exact ⟨Witness.linear .conditional case_42_28_14, case_42_28_14_checked⟩

    · exact ⟨Witness.linear .conditional case_42_28_15, case_42_28_15_checked⟩

    · exact ⟨Witness.linear .conditional case_42_28_16, case_42_28_16_checked⟩

    · exact ⟨Witness.linear .negative case_42_28_17, case_42_28_17_checked⟩

    · exact ⟨Witness.linear .conditional case_42_28_18, case_42_28_18_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_42_29_1_checked⟩

    · exact ⟨Witness.rising, case_42_29_2_checked⟩

    · exact ⟨Witness.rising, case_42_29_3_checked⟩

    · exact ⟨Witness.rising, case_42_29_4_checked⟩

    · exact ⟨Witness.rising, case_42_29_5_checked⟩

    · exact ⟨Witness.rising, case_42_29_6_checked⟩

    · exact ⟨Witness.rising, case_42_29_7_checked⟩

    · exact ⟨Witness.rising, case_42_29_8_checked⟩

    · exact ⟨Witness.linear .positive case_42_29_9, case_42_29_9_checked⟩

    · exact ⟨Witness.linear .positive case_42_29_10, case_42_29_10_checked⟩

    · exact ⟨Witness.linear .positive case_42_29_11, case_42_29_11_checked⟩

    · exact ⟨Witness.linear .positive case_42_29_12, case_42_29_12_checked⟩

    · exact ⟨Witness.linear .positive case_42_29_13, case_42_29_13_checked⟩

    · exact ⟨Witness.linear .conditional case_42_29_14, case_42_29_14_checked⟩

    · exact ⟨Witness.linear .conditional case_42_29_15, case_42_29_15_checked⟩

    · exact ⟨Witness.linear .conditional case_42_29_16, case_42_29_16_checked⟩

    · exact ⟨Witness.linear .negative case_42_29_17, case_42_29_17_checked⟩

    · exact ⟨Witness.linear .conditional case_42_29_18, case_42_29_18_checked⟩

  · have hkHi : k ≤ 19 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_42_30_1_checked⟩

    · exact ⟨Witness.rising, case_42_30_2_checked⟩

    · exact ⟨Witness.rising, case_42_30_3_checked⟩

    · exact ⟨Witness.rising, case_42_30_4_checked⟩

    · exact ⟨Witness.rising, case_42_30_5_checked⟩

    · exact ⟨Witness.rising, case_42_30_6_checked⟩

    · exact ⟨Witness.rising, case_42_30_7_checked⟩

    · exact ⟨Witness.rising, case_42_30_8_checked⟩

    · exact ⟨Witness.linear .positive case_42_30_9, case_42_30_9_checked⟩

    · exact ⟨Witness.linear .positive case_42_30_10, case_42_30_10_checked⟩

    · exact ⟨Witness.linear .positive case_42_30_11, case_42_30_11_checked⟩

    · exact ⟨Witness.linear .positive case_42_30_12, case_42_30_12_checked⟩

    · exact ⟨Witness.linear .positive case_42_30_13, case_42_30_13_checked⟩

    · exact ⟨Witness.linear .positive case_42_30_14, case_42_30_14_checked⟩

    · exact ⟨Witness.linear .conditional case_42_30_15, case_42_30_15_checked⟩

    · exact ⟨Witness.linear .conditional case_42_30_16, case_42_30_16_checked⟩

    · exact ⟨Witness.linear .negative case_42_30_17, case_42_30_17_checked⟩

    · exact ⟨Witness.linear .conditional case_42_30_18, case_42_30_18_checked⟩

    · exact ⟨Witness.linear .negative case_42_30_19, case_42_30_19_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_42_31_1_checked⟩

    · exact ⟨Witness.rising, case_42_31_2_checked⟩

    · exact ⟨Witness.rising, case_42_31_3_checked⟩

    · exact ⟨Witness.rising, case_42_31_4_checked⟩

    · exact ⟨Witness.rising, case_42_31_5_checked⟩

    · exact ⟨Witness.rising, case_42_31_6_checked⟩

    · exact ⟨Witness.rising, case_42_31_7_checked⟩

    · exact ⟨Witness.rising, case_42_31_8_checked⟩

    · exact ⟨Witness.linear .positive case_42_31_9, case_42_31_9_checked⟩

    · exact ⟨Witness.linear .positive case_42_31_10, case_42_31_10_checked⟩

    · exact ⟨Witness.linear .positive case_42_31_11, case_42_31_11_checked⟩

    · exact ⟨Witness.linear .positive case_42_31_12, case_42_31_12_checked⟩

    · exact ⟨Witness.linear .positive case_42_31_13, case_42_31_13_checked⟩

    · exact ⟨Witness.linear .positive case_42_31_14, case_42_31_14_checked⟩

    · exact ⟨Witness.linear .conditional case_42_31_15, case_42_31_15_checked⟩

    · exact ⟨Witness.linear .conditional case_42_31_16, case_42_31_16_checked⟩

    · exact ⟨Witness.linear .conditional case_42_31_17, case_42_31_17_checked⟩

    · exact ⟨Witness.linear .conditional case_42_31_18, case_42_31_18_checked⟩

    · exact ⟨Witness.linear .negative case_42_31_19, case_42_31_19_checked⟩

    · exact ⟨Witness.linear .negative case_42_31_20, case_42_31_20_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_42_32_1_checked⟩

    · exact ⟨Witness.rising, case_42_32_2_checked⟩

    · exact ⟨Witness.rising, case_42_32_3_checked⟩

    · exact ⟨Witness.rising, case_42_32_4_checked⟩

    · exact ⟨Witness.rising, case_42_32_5_checked⟩

    · exact ⟨Witness.rising, case_42_32_6_checked⟩

    · exact ⟨Witness.rising, case_42_32_7_checked⟩

    · exact ⟨Witness.rising, case_42_32_8_checked⟩

    · exact ⟨Witness.linear .positive case_42_32_9, case_42_32_9_checked⟩

    · exact ⟨Witness.linear .positive case_42_32_10, case_42_32_10_checked⟩

    · exact ⟨Witness.linear .positive case_42_32_11, case_42_32_11_checked⟩

    · exact ⟨Witness.linear .positive case_42_32_12, case_42_32_12_checked⟩

    · exact ⟨Witness.linear .positive case_42_32_13, case_42_32_13_checked⟩

    · exact ⟨Witness.linear .positive case_42_32_14, case_42_32_14_checked⟩

    · exact ⟨Witness.linear .positive case_42_32_15, case_42_32_15_checked⟩

    · exact ⟨Witness.linear .conditional case_42_32_16, case_42_32_16_checked⟩

    · exact ⟨Witness.linear .conditional case_42_32_17, case_42_32_17_checked⟩

    · exact ⟨Witness.linear .conditional case_42_32_18, case_42_32_18_checked⟩

    · exact ⟨Witness.linear .negative case_42_32_19, case_42_32_19_checked⟩

    · exact ⟨Witness.linear .negative case_42_32_20, case_42_32_20_checked⟩

  · have hkHi : k ≤ 21 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_42_33_1_checked⟩

    · exact ⟨Witness.rising, case_42_33_2_checked⟩

    · exact ⟨Witness.rising, case_42_33_3_checked⟩

    · exact ⟨Witness.rising, case_42_33_4_checked⟩

    · exact ⟨Witness.rising, case_42_33_5_checked⟩

    · exact ⟨Witness.rising, case_42_33_6_checked⟩

    · exact ⟨Witness.rising, case_42_33_7_checked⟩

    · exact ⟨Witness.rising, case_42_33_8_checked⟩

    · exact ⟨Witness.linear .positive case_42_33_9, case_42_33_9_checked⟩

    · exact ⟨Witness.linear .positive case_42_33_10, case_42_33_10_checked⟩

    · exact ⟨Witness.linear .positive case_42_33_11, case_42_33_11_checked⟩

    · exact ⟨Witness.linear .positive case_42_33_12, case_42_33_12_checked⟩

    · exact ⟨Witness.linear .positive case_42_33_13, case_42_33_13_checked⟩

    · exact ⟨Witness.linear .positive case_42_33_14, case_42_33_14_checked⟩

    · exact ⟨Witness.linear .positive case_42_33_15, case_42_33_15_checked⟩

    · exact ⟨Witness.linear .positive case_42_33_16, case_42_33_16_checked⟩

    · exact ⟨Witness.linear .conditional case_42_33_17, case_42_33_17_checked⟩

    · exact ⟨Witness.linear .conditional case_42_33_18, case_42_33_18_checked⟩

    · exact ⟨Witness.linear .negative case_42_33_19, case_42_33_19_checked⟩

    · exact ⟨Witness.linear .negative case_42_33_20, case_42_33_20_checked⟩

    · exact ⟨Witness.linear .negative case_42_33_21, case_42_33_21_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_42_34_1_checked⟩

    · exact ⟨Witness.rising, case_42_34_2_checked⟩

    · exact ⟨Witness.rising, case_42_34_3_checked⟩

    · exact ⟨Witness.rising, case_42_34_4_checked⟩

    · exact ⟨Witness.rising, case_42_34_5_checked⟩

    · exact ⟨Witness.rising, case_42_34_6_checked⟩

    · exact ⟨Witness.rising, case_42_34_7_checked⟩

    · exact ⟨Witness.rising, case_42_34_8_checked⟩

    · exact ⟨Witness.linear .positive case_42_34_9, case_42_34_9_checked⟩

    · exact ⟨Witness.linear .positive case_42_34_10, case_42_34_10_checked⟩

    · exact ⟨Witness.linear .positive case_42_34_11, case_42_34_11_checked⟩

    · exact ⟨Witness.linear .positive case_42_34_12, case_42_34_12_checked⟩

    · exact ⟨Witness.linear .positive case_42_34_13, case_42_34_13_checked⟩

    · exact ⟨Witness.linear .positive case_42_34_14, case_42_34_14_checked⟩

    · exact ⟨Witness.linear .positive case_42_34_15, case_42_34_15_checked⟩

    · exact ⟨Witness.linear .positive case_42_34_16, case_42_34_16_checked⟩

    · exact ⟨Witness.linear .conditional case_42_34_17, case_42_34_17_checked⟩

    · exact ⟨Witness.linear .conditional case_42_34_18, case_42_34_18_checked⟩

    · exact ⟨Witness.linear .negative case_42_34_19, case_42_34_19_checked⟩

    · exact ⟨Witness.linear .negative case_42_34_20, case_42_34_20_checked⟩

    · exact ⟨Witness.linear .negative case_42_34_21, case_42_34_21_checked⟩

    · exact ⟨Witness.linear .negative case_42_34_22, case_42_34_22_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_42_35_1_checked⟩

    · exact ⟨Witness.rising, case_42_35_2_checked⟩

    · exact ⟨Witness.rising, case_42_35_3_checked⟩

    · exact ⟨Witness.rising, case_42_35_4_checked⟩

    · exact ⟨Witness.rising, case_42_35_5_checked⟩

    · exact ⟨Witness.rising, case_42_35_6_checked⟩

    · exact ⟨Witness.rising, case_42_35_7_checked⟩

    · exact ⟨Witness.rising, case_42_35_8_checked⟩

    · exact ⟨Witness.linear .positive case_42_35_9, case_42_35_9_checked⟩

    · exact ⟨Witness.linear .positive case_42_35_10, case_42_35_10_checked⟩

    · exact ⟨Witness.linear .positive case_42_35_11, case_42_35_11_checked⟩

    · exact ⟨Witness.linear .positive case_42_35_12, case_42_35_12_checked⟩

    · exact ⟨Witness.linear .positive case_42_35_13, case_42_35_13_checked⟩

    · exact ⟨Witness.linear .positive case_42_35_14, case_42_35_14_checked⟩

    · exact ⟨Witness.linear .positive case_42_35_15, case_42_35_15_checked⟩

    · exact ⟨Witness.linear .positive case_42_35_16, case_42_35_16_checked⟩

    · exact ⟨Witness.linear .positive case_42_35_17, case_42_35_17_checked⟩

    · exact ⟨Witness.linear .conditional case_42_35_18, case_42_35_18_checked⟩

    · exact ⟨Witness.linear .negative case_42_35_19, case_42_35_19_checked⟩

    · exact ⟨Witness.linear .negative case_42_35_20, case_42_35_20_checked⟩

    · exact ⟨Witness.linear .negative case_42_35_21, case_42_35_21_checked⟩

    · exact ⟨Witness.linear .negative case_42_35_22, case_42_35_22_checked⟩

  · have hkHi : k ≤ 23 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_42_36_1_checked⟩

    · exact ⟨Witness.rising, case_42_36_2_checked⟩

    · exact ⟨Witness.rising, case_42_36_3_checked⟩

    · exact ⟨Witness.rising, case_42_36_4_checked⟩

    · exact ⟨Witness.rising, case_42_36_5_checked⟩

    · exact ⟨Witness.rising, case_42_36_6_checked⟩

    · exact ⟨Witness.rising, case_42_36_7_checked⟩

    · exact ⟨Witness.rising, case_42_36_8_checked⟩

    · exact ⟨Witness.linear .positive case_42_36_9, case_42_36_9_checked⟩

    · exact ⟨Witness.linear .positive case_42_36_10, case_42_36_10_checked⟩

    · exact ⟨Witness.linear .positive case_42_36_11, case_42_36_11_checked⟩

    · exact ⟨Witness.linear .positive case_42_36_12, case_42_36_12_checked⟩

    · exact ⟨Witness.linear .positive case_42_36_13, case_42_36_13_checked⟩

    · exact ⟨Witness.linear .positive case_42_36_14, case_42_36_14_checked⟩

    · exact ⟨Witness.linear .positive case_42_36_15, case_42_36_15_checked⟩

    · exact ⟨Witness.linear .positive case_42_36_16, case_42_36_16_checked⟩

    · exact ⟨Witness.linear .positive case_42_36_17, case_42_36_17_checked⟩

    · exact ⟨Witness.linear .positive case_42_36_18, case_42_36_18_checked⟩

    · exact ⟨Witness.linear .negative case_42_36_19, case_42_36_19_checked⟩

    · exact ⟨Witness.linear .negative case_42_36_20, case_42_36_20_checked⟩

    · exact ⟨Witness.linear .negative case_42_36_21, case_42_36_21_checked⟩

    · exact ⟨Witness.linear .negative case_42_36_22, case_42_36_22_checked⟩

    · exact ⟨Witness.linear .negative case_42_36_23, case_42_36_23_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_42_37_1_checked⟩

    · exact ⟨Witness.rising, case_42_37_2_checked⟩

    · exact ⟨Witness.rising, case_42_37_3_checked⟩

    · exact ⟨Witness.rising, case_42_37_4_checked⟩

    · exact ⟨Witness.rising, case_42_37_5_checked⟩

    · exact ⟨Witness.rising, case_42_37_6_checked⟩

    · exact ⟨Witness.rising, case_42_37_7_checked⟩

    · exact ⟨Witness.linear .positive case_42_37_8, case_42_37_8_checked⟩

    · exact ⟨Witness.linear .positive case_42_37_9, case_42_37_9_checked⟩

    · exact ⟨Witness.linear .positive case_42_37_10, case_42_37_10_checked⟩

    · exact ⟨Witness.linear .positive case_42_37_11, case_42_37_11_checked⟩

    · exact ⟨Witness.linear .positive case_42_37_12, case_42_37_12_checked⟩

    · exact ⟨Witness.linear .positive case_42_37_13, case_42_37_13_checked⟩

    · exact ⟨Witness.linear .positive case_42_37_14, case_42_37_14_checked⟩

    · exact ⟨Witness.linear .positive case_42_37_15, case_42_37_15_checked⟩

    · exact ⟨Witness.linear .positive case_42_37_16, case_42_37_16_checked⟩

    · exact ⟨Witness.linear .positive case_42_37_17, case_42_37_17_checked⟩

    · exact ⟨Witness.linear .positive case_42_37_18, case_42_37_18_checked⟩

    · exact ⟨Witness.linear .conditional case_42_37_19, case_42_37_19_checked⟩

    · exact ⟨Witness.linear .negative case_42_37_20, case_42_37_20_checked⟩

    · exact ⟨Witness.linear .negative case_42_37_21, case_42_37_21_checked⟩

    · exact ⟨Witness.linear .negative case_42_37_22, case_42_37_22_checked⟩

    · exact ⟨Witness.linear .negative case_42_37_23, case_42_37_23_checked⟩

    · exact ⟨Witness.linear .negative case_42_37_24, case_42_37_24_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_42_38_1_checked⟩

    · exact ⟨Witness.rising, case_42_38_2_checked⟩

    · exact ⟨Witness.rising, case_42_38_3_checked⟩

    · exact ⟨Witness.rising, case_42_38_4_checked⟩

    · exact ⟨Witness.rising, case_42_38_5_checked⟩

    · exact ⟨Witness.rising, case_42_38_6_checked⟩

    · exact ⟨Witness.rising, case_42_38_7_checked⟩

    · exact ⟨Witness.linear .positive case_42_38_8, case_42_38_8_checked⟩

    · exact ⟨Witness.linear .positive case_42_38_9, case_42_38_9_checked⟩

    · exact ⟨Witness.linear .positive case_42_38_10, case_42_38_10_checked⟩

    · exact ⟨Witness.linear .positive case_42_38_11, case_42_38_11_checked⟩

    · exact ⟨Witness.linear .positive case_42_38_12, case_42_38_12_checked⟩

    · exact ⟨Witness.linear .positive case_42_38_13, case_42_38_13_checked⟩

    · exact ⟨Witness.linear .positive case_42_38_14, case_42_38_14_checked⟩

    · exact ⟨Witness.linear .positive case_42_38_15, case_42_38_15_checked⟩

    · exact ⟨Witness.linear .positive case_42_38_16, case_42_38_16_checked⟩

    · exact ⟨Witness.linear .positive case_42_38_17, case_42_38_17_checked⟩

    · exact ⟨Witness.linear .positive case_42_38_18, case_42_38_18_checked⟩

    · exact ⟨Witness.linear .positive case_42_38_19, case_42_38_19_checked⟩

    · exact ⟨Witness.linear .negative case_42_38_20, case_42_38_20_checked⟩

    · exact ⟨Witness.linear .negative case_42_38_21, case_42_38_21_checked⟩

    · exact ⟨Witness.linear .negative case_42_38_22, case_42_38_22_checked⟩

    · exact ⟨Witness.linear .negative case_42_38_23, case_42_38_23_checked⟩

    · exact ⟨Witness.linear .negative case_42_38_24, case_42_38_24_checked⟩

  · have hkHi : k ≤ 25 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_42_39_1_checked⟩

    · exact ⟨Witness.rising, case_42_39_2_checked⟩

    · exact ⟨Witness.rising, case_42_39_3_checked⟩

    · exact ⟨Witness.rising, case_42_39_4_checked⟩

    · exact ⟨Witness.rising, case_42_39_5_checked⟩

    · exact ⟨Witness.rising, case_42_39_6_checked⟩

    · exact ⟨Witness.rising, case_42_39_7_checked⟩

    · exact ⟨Witness.linear .positive case_42_39_8, case_42_39_8_checked⟩

    · exact ⟨Witness.linear .positive case_42_39_9, case_42_39_9_checked⟩

    · exact ⟨Witness.linear .positive case_42_39_10, case_42_39_10_checked⟩

    · exact ⟨Witness.linear .positive case_42_39_11, case_42_39_11_checked⟩

    · exact ⟨Witness.linear .positive case_42_39_12, case_42_39_12_checked⟩

    · exact ⟨Witness.linear .positive case_42_39_13, case_42_39_13_checked⟩

    · exact ⟨Witness.linear .positive case_42_39_14, case_42_39_14_checked⟩

    · exact ⟨Witness.linear .positive case_42_39_15, case_42_39_15_checked⟩

    · exact ⟨Witness.linear .positive case_42_39_16, case_42_39_16_checked⟩

    · exact ⟨Witness.linear .positive case_42_39_17, case_42_39_17_checked⟩

    · exact ⟨Witness.linear .positive case_42_39_18, case_42_39_18_checked⟩

    · exact ⟨Witness.linear .positive case_42_39_19, case_42_39_19_checked⟩

    · exact ⟨Witness.linear .negative case_42_39_20, case_42_39_20_checked⟩

    · exact ⟨Witness.linear .negative case_42_39_21, case_42_39_21_checked⟩

    · exact ⟨Witness.linear .negative case_42_39_22, case_42_39_22_checked⟩

    · exact ⟨Witness.linear .negative case_42_39_23, case_42_39_23_checked⟩

    · exact ⟨Witness.linear .negative case_42_39_24, case_42_39_24_checked⟩

    · exact ⟨Witness.linear .negative case_42_39_25, case_42_39_25_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_42_40_1_checked⟩

    · exact ⟨Witness.rising, case_42_40_2_checked⟩

    · exact ⟨Witness.rising, case_42_40_3_checked⟩

    · exact ⟨Witness.rising, case_42_40_4_checked⟩

    · exact ⟨Witness.rising, case_42_40_5_checked⟩

    · exact ⟨Witness.rising, case_42_40_6_checked⟩

    · exact ⟨Witness.rising, case_42_40_7_checked⟩

    · exact ⟨Witness.linear .positive case_42_40_8, case_42_40_8_checked⟩

    · exact ⟨Witness.linear .positive case_42_40_9, case_42_40_9_checked⟩

    · exact ⟨Witness.linear .positive case_42_40_10, case_42_40_10_checked⟩

    · exact ⟨Witness.linear .positive case_42_40_11, case_42_40_11_checked⟩

    · exact ⟨Witness.linear .positive case_42_40_12, case_42_40_12_checked⟩

    · exact ⟨Witness.linear .positive case_42_40_13, case_42_40_13_checked⟩

    · exact ⟨Witness.linear .positive case_42_40_14, case_42_40_14_checked⟩

    · exact ⟨Witness.linear .positive case_42_40_15, case_42_40_15_checked⟩

    · exact ⟨Witness.linear .positive case_42_40_16, case_42_40_16_checked⟩

    · exact ⟨Witness.linear .positive case_42_40_17, case_42_40_17_checked⟩

    · exact ⟨Witness.linear .positive case_42_40_18, case_42_40_18_checked⟩

    · exact ⟨Witness.linear .positive case_42_40_19, case_42_40_19_checked⟩

    · exact ⟨Witness.linear .positive case_42_40_20, case_42_40_20_checked⟩

    · exact ⟨Witness.linear .negative case_42_40_21, case_42_40_21_checked⟩

    · exact ⟨Witness.linear .negative case_42_40_22, case_42_40_22_checked⟩

    · exact ⟨Witness.linear .negative case_42_40_23, case_42_40_23_checked⟩

    · exact ⟨Witness.linear .negative case_42_40_24, case_42_40_24_checked⟩

    · exact ⟨Witness.linear .negative case_42_40_25, case_42_40_25_checked⟩

    · exact ⟨Witness.linear .negative case_42_40_26, case_42_40_26_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_42_41_1_checked⟩

    · exact ⟨Witness.rising, case_42_41_2_checked⟩

    · exact ⟨Witness.rising, case_42_41_3_checked⟩

    · exact ⟨Witness.rising, case_42_41_4_checked⟩

    · exact ⟨Witness.rising, case_42_41_5_checked⟩

    · exact ⟨Witness.rising, case_42_41_6_checked⟩

    · exact ⟨Witness.rising, case_42_41_7_checked⟩

    · exact ⟨Witness.linear .positive case_42_41_8, case_42_41_8_checked⟩

    · exact ⟨Witness.linear .positive case_42_41_9, case_42_41_9_checked⟩

    · exact ⟨Witness.linear .positive case_42_41_10, case_42_41_10_checked⟩

    · exact ⟨Witness.linear .positive case_42_41_11, case_42_41_11_checked⟩

    · exact ⟨Witness.linear .positive case_42_41_12, case_42_41_12_checked⟩

    · exact ⟨Witness.linear .positive case_42_41_13, case_42_41_13_checked⟩

    · exact ⟨Witness.linear .positive case_42_41_14, case_42_41_14_checked⟩

    · exact ⟨Witness.linear .positive case_42_41_15, case_42_41_15_checked⟩

    · exact ⟨Witness.linear .positive case_42_41_16, case_42_41_16_checked⟩

    · exact ⟨Witness.linear .positive case_42_41_17, case_42_41_17_checked⟩

    · exact ⟨Witness.linear .positive case_42_41_18, case_42_41_18_checked⟩

    · exact ⟨Witness.linear .positive case_42_41_19, case_42_41_19_checked⟩

    · exact ⟨Witness.linear .positive case_42_41_20, case_42_41_20_checked⟩

    · exact ⟨Witness.linear .negative case_42_41_21, case_42_41_21_checked⟩

    · exact ⟨Witness.linear .negative case_42_41_22, case_42_41_22_checked⟩

    · exact ⟨Witness.linear .negative case_42_41_23, case_42_41_23_checked⟩

    · exact ⟨Witness.linear .negative case_42_41_24, case_42_41_24_checked⟩

    · exact ⟨Witness.linear .negative case_42_41_25, case_42_41_25_checked⟩

    · exact ⟨Witness.linear .negative case_42_41_26, case_42_41_26_checked⟩


#print axioms coverage_42
end ForestUnimodality.FiniteRows.FiniteData
