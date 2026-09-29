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

theorem case_50_25_1_checked :
    (Witness.rising).check 50 25 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_25_2_checked :
    (Witness.rising).check 50 25 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_25_3_checked :
    (Witness.rising).check 50 25 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_25_4_checked :
    (Witness.rising).check 50 25 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_25_5_checked :
    (Witness.rising).check 50 25 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_25_6_checked :
    (Witness.rising).check 50 25 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_25_7_checked :
    (Witness.rising).check 50 25 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_25_8_checked :
    (Witness.rising).check 50 25 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_25_9_checked :
    (Witness.rising).check 50 25 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_25_10_checked :
    (Witness.rising).check 50 25 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_25_11 : Certificate := {
  objectiveScale := 425632350000
  eta := 0
  rows := #[⟨.count 3, 4852577557868040⟩, ⟨.count 4, 831474498254400⟩, ⟨.count 5, 131980079088000⟩, ⟨.count 6, 24746264829000⟩, ⟨.count 7, 5227105763880⟩, ⟨.count 8, 1404700256960⟩, ⟨.count 9, 514844890560⟩, ⟨.count 10, 429037408800⟩, ⟨.count 12, 78656858280⟩, ⟨.path 11, 100085585600⟩, ⟨.path 12, 75166673010⟩, ⟨.privateRow 9 5, 10328678360⟩, ⟨.hall 10 1, 3660438210⟩, ⟨.hall 0 3, 3464477076060⟩, ⟨.hall 9 3, 872218908⟩, ⟨.hall 10 3, 39289140⟩, ⟨.hall 2 4, 6946319952⟩, ⟨.hall 1 5, 98406199320⟩, ⟨.hall 8 5, 373246830⟩, ⟨.hall 0 6, 3559988975400⟩, ⟨.hall 1 6, 140855932360⟩, ⟨.hall 7 7, 269467940⟩, ⟨.hall 0 8, 76273317120⟩, ⟨.hall 7 8, 9723070⟩, ⟨.hall 6 10, 3968600⟩, ⟨.hall 6 11, 391800035⟩, ⟨.hall 2 13, 578859996⟩, ⟨.hall 1 14, 357531174⟩, ⟨.hall 9 15, 3575311740⟩, ⟨.hall 5 16, 20430352800⟩, ⟨.hall 1 17, 3859066640⟩, ⟨.hall 4 20, 14077875102720⟩]
  caps := #[0, 480770999005440, 22826373778780, 10083373708980, 1763245675620, 1302640653600, 390792196080, 60691373600, 13205678200, 24009288160, 0, 5765456840, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_25_11_checked :
    (Witness.linear .positive case_50_25_11).check 50 25 11 = true := by
  change case_50_25_11.check 50 25 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_25_12 : Certificate := {
  objectiveScale := 150150000
  eta := 0
  rows := #[⟨.count 3, 2742529149360⟩, ⟨.count 4, 492123471840⟩, ⟨.count 5, 93117024000⟩, ⟨.count 6, 19088989920⟩, ⟨.count 7, 4374049680⟩, ⟨.count 8, 1143542400⟩, ⟨.count 9, 383423040⟩, ⟨.count 10, 163963800⟩, ⟨.count 11, 147987840⟩, ⟨.path 12, 8416980⟩, ⟨.path 13, 39380880⟩, ⟨.privateRow 9 7, 8744736⟩, ⟨.privateRow 10 4, 105105⟩, ⟨.privateRow 11 2, 5821200⟩, ⟨.privateRow 13 0, 3049200⟩, ⟨.hall 11 1, 4726260⟩, ⟨.hall 13 1, 3303300⟩, ⟨.hall 11 2, 152460⟩, ⟨.hall 10 3, 462000⟩, ⟨.hall 9 4, 643104⟩, ⟨.hall 0 5, 1357956600⟩, ⟨.hall 1 6, 72832760⟩, ⟨.hall 8 6, 323120⟩, ⟨.hall 0 7, 509829320⟩, ⟨.hall 7 8, 171108⟩, ⟨.hall 1 9, 420420⟩, ⟨.hall 7 9, 100352⟩, ⟨.hall 6 12, 233640⟩, ⟨.hall 6 13, 1002430⟩, ⟨.hall 5 16, 19139120⟩, ⟨.hall 2 17, 680680⟩, ⟨.hall 2 18, 8168160⟩, ⟨.hall 4 20, 14277943680⟩, ⟨.hall 1 23, 137425207920⟩]
  caps := #[0, 1013734001280, 0, 2560718160, 1125164040, 0, 59792040, 85765680, 4084080, 0, 0, 4158000, 5534100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_25_12_checked :
    (Witness.linear .positive case_50_25_12).check 50 25 12 = true := by
  change case_50_25_12.check 50 25 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_25_13 : Certificate := {
  objectiveScale := 257400000
  eta := 0
  rows := #[⟨.count 2, 412275623760⟩, ⟨.count 3, 4678432078320⟩, ⟨.count 4, 1926125641440⟩, ⟨.count 5, 386435649600⟩, ⟨.count 6, 86598832320⟩, ⟨.count 7, 20841060240⟩, ⟨.count 8, 5260295040⟩, ⟨.count 9, 1634592960⟩, ⟨.count 10, 567567000⟩, ⟨.count 11, 249729480⟩, ⟨.count 12, 261621360⟩, ⟨.path 14, 56360535⟩, ⟨.path 15, 13812120⟩, ⟨.privateRow 5 20, 19554575040⟩, ⟨.privateRow 9 9, 32792760⟩, ⟨.privateRow 10 6, 1513512⟩, ⟨.privateRow 11 4, 17886960⟩, ⟨.privateRow 11 5, 19171152⟩, ⟨.privateRow 12 2, 495495⟩, ⟨.privateRow 13 12, 3659040⟩, ⟨.privateRow 14 0, 4624620⟩, ⟨.privateRow 15 0, 3210480⟩, ⟨.privateRow 15 2, 1121120⟩, ⟨.hall 12 1, 5641020⟩, ⟨.hall 15 1, 7147140⟩, ⟨.hall 12 2, 1330560⟩, ⟨.hall 2 3, 232792560⟩, ⟨.hall 11 3, 2037420⟩, ⟨.hall 1 4, 372468096⟩, ⟨.hall 0 5, 10359268920⟩, ⟨.hall 10 5, 844200⟩, ⟨.hall 1 6, 363483120⟩, ⟨.hall 2 6, 11531520⟩, ⟨.hall 9 6, 1174824⟩, ⟨.hall 0 7, 1872550680⟩, ⟨.hall 2 7, 3783780⟩, ⟨.hall 8 8, 810656⟩, ⟨.hall 8 9, 284004⟩, ⟨.hall 7 11, 1359435⟩, ⟨.hall 7 12, 1677060⟩, ⟨.hall 1 14, 252252⟩, ⟨.hall 1 15, 840840⟩, ⟨.hall 6 15, 51441390⟩, ⟨.hall 5 18, 2291168880⟩, ⟨.hall 4 20, 2327925600⟩]
  caps := #[0, 442753542000, 0, 8264135880, 5169052980, 854327760, 0, 46432155, 136816680, 16130610, 3593535, 19170060, 6827535, 0, 865095, 36616720, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_25_13_checked :
    (Witness.linear .positive case_50_25_13).check 50 25 13 = true := by
  change case_50_25_13.check 50 25 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_25_14 : Certificate := {
  objectiveScale := 1108800000
  eta := 0
  rows := #[⟨.count 3, 27425291493600⟩, ⟨.count 4, 12260718550080⟩, ⟨.count 5, 2989056470400⟩, ⟨.count 6, 724916031840⟩, ⟨.count 7, 199147908960⟩, ⟨.count 8, 56948411520⟩, ⟨.count 9, 17435658240⟩, ⟨.count 10, 5675670000⟩, ⟨.count 11, 2164322160⟩, ⟨.count 12, 1141620480⟩, ⟨.count 13, 1141620480⟩, ⟨.path 16, 228727296⟩, ⟨.path 17, 26530560⟩, ⟨.privateRow 5 20, 229067879040⟩, ⟨.privateRow 9 10, 1043602560⟩, ⟨.privateRow 9 11, 2354352000⟩, ⟨.privateRow 10 8, 524999475⟩, ⟨.privateRow 10 9, 1543782240⟩, ⟨.privateRow 10 10, 510810300⟩, ⟨.privateRow 11 6, 270750480⟩, ⟨.privateRow 11 7, 673512840⟩, ⟨.privateRow 12 4, 134378244⟩, ⟨.privateRow 12 5, 33033000⟩, ⟨.privateRow 16 0, 22702680⟩, ⟨.privateRow 17 0, 17937920⟩, ⟨.privateRow 17 6, 13453440⟩, ⟨.privateRow 18 0, 32162130⟩, ⟨.privateRow 18 2, 14294280⟩, ⟨.privateRow 19 0, 94517280⟩, ⟨.privateRow 19 6, 661620960⟩, ⟨.privateRow 21 4, 8380532160⟩, ⟨.hall 13 1, 79999920⟩, ⟨.hall 14 1, 30270240⟩, ⟨.hall 14 2, 1681680⟩, ⟨.hall 12 3, 14719320⟩, ⟨.hall 12 4, 3925152⟩, ⟨.hall 13 4, 1693692⟩, ⟨.hall 2 5, 187867680⟩, ⟨.hall 11 5, 11263560⟩, ⟨.hall 19 5, 2095133040⟩, ⟨.hall 0 6, 35506991520⟩, ⟨.hall 1 6, 2119637520⟩, ⟨.hall 2 6, 66306240⟩, ⟨.hall 0 7, 2572970400⟩, ⟨.hall 10 7, 10116540⟩, ⟨.hall 17 7, 257297040⟩, ⟨.hall 16 8, 80720640⟩, ⟨.hall 9 9, 15612912⟩, ⟨.hall 8 11, 37884000⟩, ⟨.hall 7 13, 129369240⟩, ⟨.hall 6 16, 2728645920⟩, ⟨.hall 5 18, 21135114000⟩]
  caps := #[0, 14908809129984, 198633314880, 0, 0, 13798249920, 0, 0, 1372250880, 0, 97057296, 88120032, 25670568, 25613280, 0, 75746160, 1700496, 528792320, 0, 1039690080, 0, 0, 0, 0, 0, 0] }

theorem case_50_25_14_checked :
    (Witness.linear .positive case_50_25_14).check 50 25 14 = true := by
  change case_50_25_14.check 50 25 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_25_15 : Certificate := {
  objectiveScale := 25200000
  eta := 0
  rows := #[⟨.count 2, 883447765200⟩, ⟨.count 3, 537750813600⟩, ⟨.count 4, 139675536000⟩, ⟨.count 5, 40572417600⟩, ⟨.count 6, 12171725280⟩, ⟨.count 7, 3822698880⟩, ⟨.count 8, 1274232960⟩, ⟨.count 9, 449729280⟩, ⟨.count 10, 172972800⟩, ⟨.count 11, 75315240⟩, ⟨.count 12, 40772160⟩, ⟨.count 13, 30579120⟩, ⟨.count 14, 31711680⟩, ⟨.path 14, 3492720⟩, ⟨.privateRow 4 21, 11174042880⟩, ⟨.privateRow 12 5, 157300⟩, ⟨.privateRow 13 3, 2744280⟩, ⟨.privateRow 13 4, 1655280⟩, ⟨.privateRow 16 0, 2540538⟩, ⟨.hall 14 1, 2846844⟩, ⟨.hall 13 2, 1122264⟩, ⟨.hall 0 3, 349188840⟩, ⟨.hall 13 3, 121836⟩, ⟨.hall 14 3, 15015⟩, ⟨.hall 12 4, 454080⟩, ⟨.hall 1 5, 9626760⟩, ⟨.hall 11 5, 576180⟩, ⟨.hall 0 6, 152277840⟩, ⟨.hall 1 6, 2917200⟩, ⟨.hall 10 6, 272760⟩, ⟨.hall 10 7, 282450⟩, ⟨.hall 9 8, 376656⟩, ⟨.hall 9 9, 270216⟩, ⟨.hall 8 10, 248640⟩, ⟨.hall 8 11, 1164680⟩, ⟨.hall 7 13, 4956666⟩, ⟨.hall 6 15, 21158280⟩, ⟨.hall 5 17, 124272720⟩, ⟨.hall 4 20, 19088989920⟩, ⟨.assumptionRow 15, 26927670⟩]
  caps := #[0, 286245313200, 0, 0, 550236960, 96241080, 72054840, 11053350, 0, 0, 2342340, 0, 151580, 357060, 0, 77910, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_25_15_checked :
    (Witness.linear .conditional case_50_25_15).check 50 25 15 = true := by
  change case_50_25_15.check 50 25 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_25_16 : Certificate := {
  objectiveScale := 264600000
  eta := 0
  rows := #[⟨.count 2, 10306890594000⟩, ⟨.count 3, 3065179637520⟩, ⟨.count 4, 928842314400⟩, ⟨.count 5, 290990700000⟩, ⟨.count 6, 92884231440⟩, ⟨.count 7, 30361050720⟩, ⟨.count 8, 10063173120⟩, ⟨.count 9, 3995671680⟩, ⟨.count 10, 1627025400⟩, ⟨.count 11, 638197560⟩, ⟨.count 12, 309188880⟩, ⟨.count 13, 166486320⟩, ⟨.count 14, 138738600⟩, ⟨.count 15, 151351200⟩, ⟨.path 13, 37158660⟩, ⟨.privateRow 3 22, 125475189840⟩, ⟨.privateRow 13 4, 28255920⟩, ⟨.privateRow 17 0, 29149120⟩, ⟨.hall 15 1, 27747720⟩, ⟨.hall 14 2, 13565552⟩, ⟨.hall 15 2, 735735⟩, ⟨.hall 13 3, 10642632⟩, ⟨.hall 14 3, 840840⟩, ⟨.hall 0 4, 3259095840⟩, ⟨.hall 12 4, 2010624⟩, ⟨.hall 12 5, 6086850⟩, ⟨.hall 13 5, 978120⟩, ⟨.hall 11 6, 8329860⟩, ⟨.hall 10 7, 3721305⟩, ⟨.hall 10 8, 5920320⟩, ⟨.hall 9 9, 7056504⟩, ⟨.hall 9 10, 7711200⟩, ⟨.hall 8 11, 4946480⟩, ⟨.hall 8 12, 44270688⟩, ⟨.hall 11 12, 10672200⟩, ⟨.hall 7 13, 68690622⟩, ⟨.hall 6 15, 291801510⟩, ⟨.hall 5 17, 1812650840⟩, ⟨.hall 4 19, 17226649440⟩, ⟨.hall 3 21, 285985659960⟩, ⟨.assumptionRow 16, 133464240⟩]
  caps := #[0, 1744243023600, 130739883120, 39673224360, 2605957200, 0, 0, 0, 142942800, 0, 0, 16396380, 0, 5155920, 8731800, 370440, 0, 2257920, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_25_16_checked :
    (Witness.linear .conditional case_50_25_16).check 50 25 16 = true := by
  change case_50_25_16.check 50 25 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_26_1_checked :
    (Witness.rising).check 50 26 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_26_2_checked :
    (Witness.rising).check 50 26 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_26_3_checked :
    (Witness.rising).check 50 26 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_26_4_checked :
    (Witness.rising).check 50 26 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_26_5_checked :
    (Witness.rising).check 50 26 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_26_6_checked :
    (Witness.rising).check 50 26 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_26_7_checked :
    (Witness.rising).check 50 26 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_26_8_checked :
    (Witness.rising).check 50 26 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_26_9_checked :
    (Witness.rising).check 50 26 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_26_10_checked :
    (Witness.rising).check 50 26 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_26_11 : Certificate := {
  objectiveScale := 7824960000
  eta := 2631967582083840
  rows := #[⟨.count 2, 637557364604160⟩, ⟨.count 3, 106445329230240⟩, ⟨.count 4, 15604550881920⟩, ⟨.count 5, 2521143424800⟩, ⟨.count 6, 477690333120⟩, ⟨.count 7, 101031971040⟩, ⟨.count 8, 26072766720⟩, ⟨.count 9, 9489720240⟩, ⟨.count 10, 8051883840⟩, ⟨.count 12, 834261120⟩, ⟨.path 11, 1956240000⟩, ⟨.path 12, 1304214912⟩, ⟨.privateRow 7 11, 2327925600⟩, ⟨.privateRow 7 12, 5819814000⟩, ⟨.privateRow 8 8, 1063127520⟩, ⟨.privateRow 8 9, 2070484416⟩, ⟨.privateRow 8 10, 2875672800⟩, ⟨.privateRow 9 5, 405543600⟩, ⟨.privateRow 9 6, 798798000⟩, ⟨.privateRow 9 7, 1080555840⟩, ⟨.privateRow 9 8, 1246124880⟩, ⟨.privateRow 10 2, 172540368⟩, ⟨.privateRow 10 3, 353296944⟩, ⟨.privateRow 10 4, 163692144⟩, ⟨.privateRow 11 0, 125810685⟩, ⟨.privateRow 12 0, 34760880⟩, ⟨.hall 7 8, 1191680⟩, ⟨.hall 7 9, 571536⟩, ⟨.hall 6 10, 879984⟩, ⟨.hall 6 11, 2677752⟩, ⟨.hall 5 16, 134067648⟩, ⟨.hall 8 17, 3578615040⟩, ⟨.hall 4 19, 3377608416⟩]
  caps := #[0, 0, 1998238125312, 174195347040, 17559210240, 0, 0, 0, 1217054592, 384319680, 144098064, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_26_11_checked :
    (Witness.linear .positive case_50_26_11).check 50 26 11 = true := by
  change case_50_26_11.check 50 26 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_26_12 : Certificate := {
  objectiveScale := 153153000000
  eta := 73906589693336400
  rows := #[⟨.count 2, 19974753971172000⟩, ⟨.count 3, 3742305684717600⟩, ⟨.count 4, 631612773792000⟩, ⟨.count 5, 113915875273200⟩, ⟨.count 6, 22438874858400⟩, ⟨.count 7, 4986416635200⟩, ⟨.count 8, 1303638336000⟩, ⟨.count 9, 403313110200⟩, ⟨.count 10, 171102531600⟩, ⟨.count 11, 153643089600⟩, ⟨.path 12, 15134579460⟩, ⟨.path 13, 36219152970⟩, ⟨.privateRow 8 10, 86003918000⟩, ⟨.privateRow 8 11, 118142224200⟩, ⟨.privateRow 8 12, 47722474800⟩, ⟨.privateRow 9 7, 21850756200⟩, ⟨.privateRow 9 8, 45627341760⟩, ⟨.privateRow 9 9, 72424352000⟩, ⟨.privateRow 9 10, 78931227375⟩, ⟨.privateRow 10 4, 4700619000⟩, ⟨.privateRow 10 5, 16499172690⟩, ⟨.privateRow 10 6, 24887640960⟩, ⟨.privateRow 10 7, 32020616628⟩, ⟨.privateRow 10 8, 4888643760⟩, ⟨.privateRow 11 2, 7482618000⟩, ⟨.privateRow 11 3, 9938451600⟩, ⟨.privateRow 11 4, 2182430250⟩, ⟨.privateRow 12 0, 4727479680⟩, ⟨.privateRow 13 0, 2638102500⟩, ⟨.privateRow 14 11, 18332414100⟩, ⟨.hall 7 10, 153605200⟩, ⟨.hall 8 10, 18806200⟩, ⟨.hall 8 11, 83098400⟩, ⟨.hall 6 12, 205696260⟩, ⟨.hall 6 13, 297335610⟩, ⟨.hall 9 16, 140189049000⟩, ⟨.hall 5 17, 26100480120⟩, ⟨.hall 4 20, 1367127216000⟩]
  caps := #[0, 0, 0, 582737975820, 1305966261600, 0, 271369612800, 45730805120, 0, 14887980590, 16318715742, 0, 13306875120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_26_12_checked :
    (Witness.linear .positive case_50_26_12).check 50 26 12 = true := by
  change case_50_26_12.check 50 26 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_26_13 : Certificate := {
  objectiveScale := 2322820500000
  eta := 1506096449426368800
  rows := #[⟨.count 2, 447087101928667200⟩, ⟨.count 3, 93605013075974400⟩, ⟨.count 4, 17829526300185600⟩, ⟨.count 5, 3636284969116800⟩, ⟨.count 6, 814922947238400⟩, ⟨.count 7, 194470248772800⟩, ⟨.count 8, 49147165267200⟩, ⟨.count 9, 15252568531200⟩, ⟨.count 10, 5084189510400⟩, ⟨.count 11, 2496700206000⟩, ⟨.count 12, 2304646344000⟩, ⟨.path 14, 549186237600⟩, ⟨.path 15, 81572691200⟩, ⟨.privateRow 8 11, 1509368760900⟩, ⟨.privateRow 8 12, 5265767707200⟩, ⟨.privateRow 9 9, 1435812778400⟩, ⟨.privateRow 9 10, 2542094755200⟩, ⟨.privateRow 9 11, 3011171763600⟩, ⟨.privateRow 10 6, 190657106640⟩, ⟨.privateRow 10 7, 673655110128⟩, ⟨.privateRow 10 8, 1362845243760⟩, ⟨.privateRow 10 9, 2017787711940⟩, ⟨.privateRow 11 4, 196709713200⟩, ⟨.privateRow 11 5, 383790279600⟩, ⟨.privateRow 11 6, 599208049440⟩, ⟨.privateRow 11 7, 691005915600⟩, ⟨.privateRow 12 2, 165461788800⟩, ⟨.privateRow 12 3, 236866429800⟩, ⟨.privateRow 12 4, 69837768000⟩, ⟨.privateRow 13 0, 101514184200⟩, ⟨.privateRow 14 0, 41902660800⟩, ⟨.privateRow 15 0, 47664276660⟩, ⟨.hall 9 9, 495073215⟩, ⟨.hall 8 10, 6279036400⟩, ⟨.hall 9 10, 3165107400⟩, ⟨.hall 7 11, 2489587100⟩, ⟨.hall 7 12, 13702088400⟩, ⟨.hall 6 15, 176919282540⟩, ⟨.hall 10 15, 3336499366200⟩, ⟨.hall 5 18, 5034471670800⟩, ⟨.hall 4 21, 810433013644800⟩]
  caps := #[0, 0, 0, 0, 54533985105600, 20220291218400, 9979114974400, 360130090320, 2471016447900, 0, 949494441714, 0, 275912852600, 0, 166222056000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_26_13_checked :
    (Witness.linear .positive case_50_26_13).check 50 26 13 = true := by
  change case_50_26_13.check 50 26 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_26_14 : Certificate := {
  objectiveScale := 23823800000
  eta := 17577783494631360
  rows := #[⟨.count 2, 5488715004252480⟩, ⟨.count 3, 1250593292108160⟩, ⟨.count 4, 272495796693120⟩, ⟨.count 5, 67221645210720⟩, ⟨.count 6, 16526409419520⟩, ⟨.count 7, 4432370342400⟩, ⟨.count 8, 1277565569280⟩, ⟨.count 9, 381314213280⟩, ⟨.count 10, 127104737760⟩, ⟨.count 11, 46092926880⟩, ⟨.count 12, 21273658560⟩, ⟨.count 13, 23046463440⟩, ⟨.path 15, 438357920⟩, ⟨.path 16, 4758378240⟩, ⟨.privateRow 4 22, 8120735663040⟩, ⟨.privateRow 8 12, 25607181600⟩, ⟨.privateRow 9 10, 20980429470⟩, ⟨.privateRow 9 11, 74028034080⟩, ⟨.privateRow 9 12, 26072766720⟩, ⟨.privateRow 10 8, 11624108496⟩, ⟨.privateRow 10 9, 34953802884⟩, ⟨.privateRow 10 10, 27097053984⟩, ⟨.privateRow 11 6, 6006048048⟩, ⟨.privateRow 11 7, 16993856880⟩, ⟨.privateRow 11 8, 30728617920⟩, ⟨.privateRow 12 4, 3169560240⟩, ⟨.privateRow 12 5, 2481926832⟩, ⟨.privateRow 12 6, 27051689280⟩, ⟨.privateRow 12 7, 1846671750⟩, ⟨.privateRow 13 2, 1969783200⟩, ⟨.privateRow 13 3, 4405151520⟩, ⟨.privateRow 13 4, 2777394312⟩, ⟨.privateRow 14 0, 2148854400⟩, ⟨.privateRow 15 0, 570341772⟩, ⟨.privateRow 16 0, 444422160⟩, ⟨.privateRow 17 0, 651819168⟩, ⟨.privateRow 18 0, 1758877120⟩, ⟨.hall 10 8, 50329860⟩, ⟨.hall 9 9, 192675105⟩, ⟨.hall 10 9, 70326144⟩, ⟨.hall 8 11, 415960160⟩, ⟨.hall 7 13, 664343680⟩, ⟨.hall 12 13, 16208501760⟩, ⟨.hall 7 14, 1719125408⟩, ⟨.hall 11 14, 87576561072⟩, ⟨.hall 6 16, 18488630160⟩, ⟨.hall 5 18, 123133961808⟩, ⟨.hall 4 21, 20424880607040⟩]
  caps := #[0, 0, 0, 898730497280, 401334373440, 305978778560, 0, 0, 13665331680, 2712496920, 0, 5697752060, 7607356900, 777336560, 774077920, 2101578248, 0, 10429106688, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_26_14_checked :
    (Witness.linear .positive case_50_26_14).check 50 26 14 = true := by
  change case_50_26_14.check 50 26 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_26_15 : Certificate := {
  objectiveScale := 476974575000
  eta := 202144510188260640
  rows := #[⟨.count 2, 54331330801587840⟩, ⟨.count 3, 14381822859243840⟩, ⟨.count 4, 3901562334109440⟩, ⟨.count 5, 1068779043652320⟩, ⟨.count 6, 304741290934080⟩, ⟨.count 7, 94298679034560⟩, ⟨.count 8, 30583355362560⟩, ⟨.count 9, 10456809002640⟩, ⟨.count 10, 3822919420320⟩, ⟨.count 11, 1590205977360⟩, ⟨.count 12, 815490244800⟩, ⟨.count 13, 706758212160⟩, ⟨.count 14, 674632838880⟩, ⟨.path 14, 66360645120⟩, ⟨.privateRow 3 23, 435812813916480⟩, ⟨.privateRow 9 10, 74959204320⟩, ⟨.privateRow 10 8, 29983681728⟩, ⟨.privateRow 10 9, 736474182444⟩, ⟨.privateRow 10 10, 1098687766176⟩, ⟨.privateRow 11 5, 1460244240⟩, ⟨.privateRow 11 7, 308760532080⟩, ⟨.privateRow 11 8, 845298884430⟩, ⟨.privateRow 12 5, 133196739984⟩, ⟨.privateRow 12 6, 415295958000⟩, ⟨.privateRow 12 7, 756027414450⟩, ⟨.privateRow 12 8, 297071446320⟩, ⟨.privateRow 13 3, 63015155280⟩, ⟨.privateRow 13 4, 202513410792⟩, ⟨.privateRow 13 5, 383582448480⟩, ⟨.privateRow 14 1, 37479602160⟩, ⟨.privateRow 14 2, 115359294960⟩, ⟨.privateRow 14 3, 22487761296⟩, ⟨.privateRow 15 0, 50597462916⟩, ⟨.privateRow 16 0, 44294075280⟩, ⟨.hall 10 7, 4348594866⟩, ⟨.hall 9 8, 622861344⟩, ⟨.hall 10 8, 2385065592⟩, ⟨.hall 9 9, 8701750701⟩, ⟨.hall 11 9, 2706533280⟩, ⟨.hall 8 10, 6249169920⟩, ⟨.hall 11 10, 2471182560⟩, ⟨.hall 8 11, 9960104000⟩, ⟨.hall 7 13, 10301411120⟩, ⟨.hall 12 13, 815490244800⟩, ⟨.hall 7 14, 117918280480⟩, ⟨.hall 6 16, 756468000288⟩, ⟨.hall 5 18, 5518527217632⟩, ⟨.hall 4 20, 59473939973760⟩, ⟨.hall 3 22, 1061109459970560⟩, ⟨.assumptionRow 15, 581990950464⟩]
  caps := #[0, 8360770900980960, 639212885011008, 99977895878784, 0, 924045970848, 0, 0, 16258219208, 367957638048, 72937373082, 59394239520, 179682091182, 0, 0, 173689408200, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_26_15_checked :
    (Witness.linear .conditional case_50_26_15).check 50 26 15 = true := by
  change case_50_26_15.check 50 26 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_26_16 : Certificate := {
  objectiveScale := 3276189000000
  eta := 643187077871738400
  rows := #[⟨.count 2, 175777834946313600⟩, ⟨.count 3, 52297537669977600⟩, ⟨.count 4, 15564743354160000⟩, ⟨.count 5, 4928835395484000⟩, ⟨.count 6, 1605626156534400⟩, ⟨.count 7, 547951783579200⟩, ⟨.count 8, 191895563059200⟩, ⟨.count 9, 69149865985200⟩, ⟨.count 10, 25860925490400⟩, ⟨.count 11, 10601373182400⟩, ⟨.count 12, 4892941468800⟩, ⟨.count 13, 2650343295600⟩, ⟨.count 14, 2248776129600⟩, ⟨.count 15, 1686582097200⟩, ⟨.count 17, 6371532367200⟩, ⟨.path 13, 340486686540⟩, ⟨.privateRow 3 23, 3268596104373600⟩, ⟨.privateRow 10 9, 1574143290720⟩, ⟨.privateRow 11 7, 330177447600⟩, ⟨.privateRow 11 8, 3754653002100⟩, ⟨.privateRow 11 9, 4761439254000⟩, ⟨.privateRow 12 6, 1396904586000⟩, ⟨.privateRow 12 7, 4400249445900⟩, ⟨.privateRow 12 8, 5572516672800⟩, ⟨.privateRow 13 4, 394153618320⟩, ⟨.privateRow 13 5, 1993420598400⟩, ⟨.privateRow 13 6, 4196376884700⟩, ⟨.privateRow 13 7, 4990023640800⟩, ⟨.privateRow 14 2, 80313433200⟩, ⟨.privateRow 14 3, 875416421880⟩, ⟨.privateRow 14 4, 2132767837200⟩, ⟨.privateRow 14 5, 1094270527350⟩, ⟨.privateRow 15 1, 419090096880⟩, ⟨.privateRow 15 2, 528462390456⟩, ⟨.privateRow 16 0, 170361828000⟩, ⟨.hall 11 7, 38749515420⟩, ⟨.hall 10 8, 71584729650⟩, ⟨.hall 11 8, 14611357200⟩, ⟨.hall 9 9, 57809318490⟩, ⟨.hall 10 9, 15823992870⟩, ⟨.hall 9 10, 69217063650⟩, ⟨.hall 8 11, 45789559200⟩, ⟨.hall 8 12, 278425285600⟩, ⟨.hall 12 13, 21726990093600⟩, ⟨.hall 7 14, 1279347589520⟩, ⟨.hall 11 14, 8834477652000⟩, ⟨.hall 6 16, 6324471513360⟩, ⟨.hall 5 18, 45731998643760⟩, ⟨.hall 4 20, 516578783760000⟩, ⟨.hall 3 21, 501701510091600⟩, ⟨.hall 2 23, 4993688492793000⟩, ⟨.assumptionRow 16, 2392027493625⟩]
  caps := #[0, 0, 3535293745728360, 0, 34957999865250, 0, 19317032151300, 0, 1910719981170, 1923295374000, 102287044860, 32499431250, 433007865045, 538357804380, 223367445840, 705445396425, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_26_16_checked :
    (Witness.linear .conditional case_50_26_16).check 50 26 16 = true := by
  change case_50_26_16.check 50 26 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_27_1_checked :
    (Witness.rising).check 50 27 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_27_2_checked :
    (Witness.rising).check 50 27 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_27_3_checked :
    (Witness.rising).check 50 27 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_27_4_checked :
    (Witness.rising).check 50 27 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_27_5_checked :
    (Witness.rising).check 50 27 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_27_6_checked :
    (Witness.rising).check 50 27 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_27_7_checked :
    (Witness.rising).check 50 27 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_27_8_checked :
    (Witness.rising).check 50 27 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_27_9_checked :
    (Witness.rising).check 50 27 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_27_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_27_10_checked :
    (Witness.linear .positive case_50_27_10).check 50 27 10 = true := by
  change case_50_27_10.check 50 27 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_27_11 : Certificate := {
  objectiveScale := 12443184000000
  eta := 5537001800808878400
  rows := #[⟨.count 2, 1222454943035726400⟩, ⟨.count 3, 179202078484228800⟩, ⟨.count 4, 26252533790683200⟩, ⟨.count 5, 4265285810385600⟩, ⟨.count 6, 800992640448000⟩, ⟨.count 7, 164910249504000⟩, ⟨.count 8, 41227562376000⟩, ⟨.count 9, 14841922455360⟩, ⟨.count 10, 12368268712800⟩, ⟨.path 11, 3289026312000⟩, ⟨.path 12, 1978598922300⟩, ⟨.privateRow 4 23, 913131610110720⟩, ⟨.privateRow 5 18, 19223823370752⟩, ⟨.privateRow 6 15, 33374693352000⟩, ⟨.privateRow 6 16, 50618284917200⟩, ⟨.privateRow 6 17, 60741941900640⟩, ⟨.privateRow 7 11, 3180411954720⟩, ⟨.privateRow 7 12, 10208729731200⟩, ⟨.privateRow 7 13, 16491024950400⟩, ⟨.privateRow 7 14, 22548952483200⟩, ⟨.privateRow 7 15, 24736537425600⟩, ⟨.privateRow 7 16, 27092398132800⟩, ⟨.privateRow 8 8, 987743681925⟩, ⟨.privateRow 8 9, 4872348280800⟩, ⟨.privateRow 8 10, 4895773032150⟩, ⟨.privateRow 8 11, 114521006600⟩, ⟨.privateRow 8 12, 22030978644675⟩, ⟨.privateRow 9 5, 628229521920⟩, ⟨.privateRow 9 7, 4764073874560⟩, ⟨.privateRow 9 8, 1399238480640⟩, ⟨.privateRow 10 2, 276077426625⟩, ⟨.privateRow 10 3, 647861694480⟩, ⟨.privateRow 10 4, 290275694280⟩, ⟨.privateRow 11 0, 263835079200⟩, ⟨.privateRow 12 0, 124588787400⟩, ⟨.hall 5 17, 119081270880⟩, ⟨.hall 5 18, 39009381840⟩, ⟨.hall 4 20, 8163702518400⟩, ⟨.hall 6 20, 108706144060800⟩]
  caps := #[0, 4860829039809600, 1631502379821600, 104805205876800, 65360219272920, 17320578174900, 0, 1918555984800, 2392893157850, 951117642540, 788934234465, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_27_11_checked :
    (Witness.linear .positive case_50_27_11).check 50 27 11 = true := by
  change case_50_27_11.check 50 27 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_27_12 : Certificate := {
  objectiveScale := 63148800000
  eta := 41359490575603200
  rows := #[⟨.count 2, 9998058672201600⟩, ⟨.count 3, 1635824007417600⟩, ⟨.count 4, 278334234097920⟩, ⟨.count 5, 50115582316800⟩, ⟨.count 6, 9851781139200⟩, ⟨.count 7, 2204682480000⟩, ⟨.count 8, 573217444800⟩, ⟨.count 9, 158737138560⟩, ⟨.count 10, 75589113600⟩, ⟨.count 11, 63960019200⟩, ⟨.path 12, 7320058200⟩, ⟨.path 13, 14239265040⟩, ⟨.privateRow 4 23, 12818023938720⟩, ⟨.privateRow 6 16, 464033169600⟩, ⟨.privateRow 6 17, 820981761600⟩, ⟨.privateRow 7 13, 133855722000⟩, ⟨.privateRow 7 14, 233966304000⟩, ⟨.privateRow 7 15, 363247684800⟩, ⟨.privateRow 7 16, 496368512640⟩, ⟨.privateRow 8 10, 34723749060⟩, ⟨.privateRow 8 11, 71039768800⟩, ⟨.privateRow 8 12, 112989977100⟩, ⟨.privateRow 8 13, 51967515600⟩, ⟨.privateRow 8 14, 366528462300⟩, ⟨.privateRow 8 15, 77163886800⟩, ⟨.privateRow 9 7, 8573765200⟩, ⟨.privateRow 9 8, 22447676160⟩, ⟨.privateRow 9 9, 36156792672⟩, ⟨.privateRow 9 10, 21556895360⟩, ⟨.privateRow 9 11, 108764335680⟩, ⟨.privateRow 10 4, 1754747280⟩, ⟨.privateRow 10 5, 5669183520⟩, ⟨.privateRow 10 6, 16850073240⟩, ⟨.privateRow 10 7, 15117822720⟩, ⟨.privateRow 10 8, 2456646192⟩, ⟨.privateRow 11 2, 3294910080⟩, ⟨.privateRow 11 3, 4360910400⟩, ⟨.privateRow 12 0, 1748906775⟩, ⟨.privateRow 13 0, 969091200⟩, ⟨.hall 13 1, 1079844480⟩, ⟨.hall 6 13, 6972680⟩, ⟨.hall 6 14, 97617520⟩, ⟨.hall 5 17, 2293449600⟩, ⟨.hall 7 19, 343930466880⟩, ⟨.hall 4 20, 102936637440⟩]
  caps := #[0, 246958823716800, 0, 0, 0, 729305834400, 243374040000, 0, 0, 11079959280, 0, 11748657600, 1108155525, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_27_12_checked :
    (Witness.linear .positive case_50_27_12).check 50 27 12 = true := by
  change case_50_27_12.check 50 27 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_27_13 : Certificate := {
  objectiveScale := 587086500000
  eta := 527333504838940800
  rows := #[⟨.count 2, 135101972314108800⟩, ⟨.count 3, 24488529543878400⟩, ⟨.count 4, 4731681979664640⟩, ⟨.count 5, 972113795452800⟩, ⟨.count 6, 214811662665600⟩, ⟨.count 7, 50972258937600⟩, ⟨.count 8, 12743064734400⟩, ⟨.count 9, 4047797033280⟩, ⟨.count 10, 1285014931200⟩, ⟨.count 11, 543660163200⟩, ⟨.count 12, 543660163200⟩, ⟨.path 14, 147216692480⟩, ⟨.path 15, 12900814080⟩, ⟨.privateRow 4 23, 300918371513760⟩, ⟨.privateRow 7 14, 2570029862400⟩, ⟨.privateRow 7 15, 5889651768000⟩, ⟨.privateRow 7 16, 856676620800⟩, ⟨.privateRow 8 11, 322741018600⟩, ⟨.privateRow 8 12, 1581170716125⟩, ⟨.privateRow 8 13, 2824355734200⟩, ⟨.privateRow 8 15, 7702058243880⟩, ⟨.privateRow 9 11, 3922865026080⟩, ⟨.privateRow 9 12, 492589056960⟩, ⟨.privateRow 9 13, 524714430240⟩, ⟨.privateRow 9 14, 2728515037248⟩, ⟨.privateRow 10 10, 2746719415440⟩, ⟨.privateRow 11 6, 4493059200⟩, ⟨.privateRow 11 10, 931988851200⟩, ⟨.privateRow 12 2, 30742687800⟩, ⟨.privateRow 12 10, 188770890000⟩, ⟨.privateRow 13 0, 16474550400⟩, ⟨.privateRow 13 9, 16474550400⟩, ⟨.privateRow 14 0, 11473347600⟩, ⟨.privateRow 15 9, 24986401440⟩, ⟨.privateRow 16 7, 56219403240⟩, ⟨.privateRow 17 6, 42833831040⟩, ⟨.privateRow 17 8, 71389718400⟩, ⟨.hall 14 1, 3844061760⟩, ⟨.hall 7 12, 961015440⟩, ⟨.hall 6 15, 13709867600⟩, ⟨.hall 7 17, 102575753280⟩, ⟨.hall 8 17, 519454135200⟩, ⟨.hall 5 18, 321780738240⟩, ⟨.hall 4 21, 21819350367360⟩]
  caps := #[0, 0, 0, 98341716753280, 0, 5279011017280, 1392857294400, 0, 1094753895235, 0, 36374761280, 134466280000, 70451290800, 152026890400, 0, 420371360640, 18739801080, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_27_13_checked :
    (Witness.linear .positive case_50_27_13).check 50 27 13 = true := by
  change case_50_27_13.check 50 27 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_27_14 : Certificate := {
  objectiveScale := 2514111600000
  eta := 2908324178202643200
  rows := #[⟨.count 2, 717638433582470400⟩, ⟨.count 3, 174013830699508800⟩, ⟨.count 4, 41277699375232320⟩, ⟨.count 5, 9655602193036800⟩, ⟨.count 6, 2484897623208000⟩, ⟨.count 7, 643149973065600⟩, ⟨.count 8, 165659841547200⟩, ⟨.count 9, 49697952464160⟩, ⟨.count 10, 14617044842400⟩, ⟨.count 11, 5300686591200⟩, ⟨.count 12, 1766895530400⟩, ⟨.count 13, 2088149263200⟩, ⟨.path 15, 497329953120⟩, ⟨.privateRow 8 15, 179789651561520⟩, ⟨.privateRow 8 16, 44155656294750⟩, ⟨.privateRow 8 17, 208292889004200⟩, ⟨.privateRow 8 18, 535653789120450⟩, ⟨.privateRow 8 19, 1736992162105200⟩, ⟨.privateRow 9 14, 110374929721056⟩, ⟨.privateRow 9 17, 764796268476240⟩, ⟨.privateRow 10 16, 585621460864440⟩, ⟨.privateRow 14 3, 56949525360⟩, ⟨.privateRow 15 0, 49972802880⟩, ⟨.privateRow 16 0, 50753627925⟩, ⟨.hall 12 3, 2471182560⟩, ⟨.hall 12 6, 117675360⟩, ⟨.hall 11 9, 2581503210⟩, ⟨.hall 6 16, 1082046268160⟩, ⟨.hall 5 18, 6022376624160⟩, ⟨.hall 4 21, 376957987267680⟩]
  caps := #[0, 27005802404380800, 893013987465600, 0, 89187175197120, 58258355675520, 4238792157600, 928066339200, 1218087070200, 574424218368, 937492876320, 357501144000, 747216069600, 462309207360, 1768112651760, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_27_14_checked :
    (Witness.linear .positive case_50_27_14).check 50 27 14 = true := by
  change case_50_27_14.check 50 27 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_27_15 : Certificate := {
  objectiveScale := 148764000000
  eta := 143818228592438400
  rows := #[⟨.count 2, 34138670423457600⟩, ⟨.count 3, 8093666544163200⟩, ⟨.count 4, 2179064069582400⟩, ⟨.count 5, 589821853420800⟩, ⟨.count 6, 163839403728000⟩, ⟨.count 7, 47224298721600⟩, ⟨.count 8, 14242248820800⟩, ⟨.count 9, 4497552259200⟩, ⟨.count 10, 1606268664000⟩, ⟨.count 11, 679575204000⟩, ⟨.count 12, 271830081600⟩, ⟨.count 13, 160626866400⟩, ⟨.count 14, 224877612960⟩, ⟨.path 13, 29745716000⟩, ⟨.privateRow 3 24, 553413097036800⟩, ⟨.privateRow 6 17, 8009926404480⟩, ⟨.privateRow 7 15, 3747960216000⟩, ⟨.privateRow 7 16, 13000067720640⟩, ⟨.privateRow 8 13, 1592883091800⟩, ⟨.privateRow 8 14, 5137828796100⟩, ⟨.privateRow 8 15, 9950834373480⟩, ⟨.privateRow 9 11, 655893037800⟩, ⟨.privateRow 9 12, 2077440805440⟩, ⟨.privateRow 9 13, 4043632633040⟩, ⟨.privateRow 9 14, 5961755383584⟩, ⟨.privateRow 10 9, 267711444000⟩, ⟨.privateRow 10 10, 863369406900⟩, ⟨.privateRow 10 11, 1711823461920⟩, ⟨.privateRow 10 12, 2586092549040⟩, ⟨.privateRow 10 13, 3132223894800⟩, ⟨.privateRow 11 7, 112438806480⟩, ⟨.privateRow 11 8, 372050263200⟩, ⟨.privateRow 11 9, 605439727200⟩, ⟨.privateRow 11 10, 1491535188000⟩, ⟨.privateRow 11 11, 1140862615200⟩, ⟨.privateRow 12 5, 49423651200⟩, ⟨.privateRow 12 6, 169893801000⟩, ⟨.privateRow 12 7, 356147745800⟩, ⟨.privateRow 12 8, 478534206150⟩, ⟨.privateRow 13 3, 24711825600⟩, ⟨.privateRow 13 4, 84244860000⟩, ⟨.privateRow 13 5, 154448910000⟩, ⟨.privateRow 14 1, 14827095360⟩, ⟨.privateRow 14 2, 41495273820⟩, ⟨.privateRow 15 0, 15376247040⟩, ⟨.privateRow 16 0, 11712375675⟩, ⟨.hall 8 14, 17514977480⟩, ⟨.hall 7 15, 9785695920⟩, ⟨.hall 8 15, 10104794700⟩, ⟨.hall 9 15, 14238574350⟩, ⟨.hall 7 16, 135568633200⟩, ⟨.hall 9 17, 9894614970240⟩, ⟨.hall 6 18, 1913969085600⟩, ⟨.hall 5 19, 3085287472800⟩, ⟨.hall 4 20, 3870923060160⟩, ⟨.hall 3 23, 856060884478800⟩, ⟨.assumptionRow 15, 188829120480⟩]
  caps := #[0, 0, 0, 44415937030080, 0, 0, 0, 0, 0, 40559016960, 0, 0, 183947660050, 57947970080, 40307287020, 0, 8215491900, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_27_15_checked :
    (Witness.linear .conditional case_50_27_15).check 50 27 15 = true := by
  change case_50_27_15.check 50 27 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_27_16 : Certificate := {
  objectiveScale := 188434400000
  eta := 95878819061625600
  rows := #[⟨.count 2, 24696059455267200⟩, ⟨.count 3, 7056016987219200⟩, ⟨.count 4, 2013040140471360⟩, ⟨.count 5, 595283166878400⟩, ⟨.count 6, 180223344100800⟩, ⟨.count 7, 55469811196800⟩, ⟨.count 8, 17990209036800⟩, ⟨.count 9, 6071695549920⟩, ⟨.count 10, 2248776129600⟩, ⟨.count 11, 951405285600⟩, ⟨.count 12, 407745122400⟩, ⟨.count 13, 160626866400⟩, ⟨.count 14, 224877612960⟩, ⟨.path 13, 22904201320⟩, ⟨.privateRow 3 24, 968472919814400⟩, ⟨.privateRow 6 17, 3337469335200⟩, ⟨.privateRow 7 15, 1142235494400⟩, ⟨.privateRow 7 16, 12785898565440⟩, ⟨.privateRow 8 13, 334639305000⟩, ⟨.privateRow 8 14, 4458511006950⟩, ⟨.privateRow 8 15, 12152761000380⟩, ⟨.privateRow 9 11, 71835904140⟩, ⟨.privateRow 9 12, 1559865347040⟩, ⟨.privateRow 9 13, 4585004664240⟩, ⟨.privateRow 9 14, 8575332974208⟩, ⟨.privateRow 10 10, 546131345760⟩, ⟨.privateRow 10 11, 1782958217040⟩, ⟨.privateRow 10 12, 3590010464040⟩, ⟨.privateRow 10 13, 5451675845616⟩, ⟨.privateRow 10 14, 1975710456720⟩, ⟨.privateRow 11 8, 172982779200⟩, ⟨.privateRow 11 9, 707376007800⟩, ⟨.privateRow 11 10, 1535663448000⟩, ⟨.privateRow 11 11, 2483538472800⟩, ⟨.privateRow 11 12, 3153228946560⟩, ⟨.privateRow 12 6, 58896517680⟩, ⟨.privateRow 12 7, 276863972000⟩, ⟨.privateRow 12 8, 621528155325⟩, ⟨.privateRow 12 9, 1310609322000⟩, ⟨.privateRow 12 10, 1094871162000⟩, ⟨.privateRow 13 4, 17972236800⟩, ⟨.privateRow 13 5, 118616762880⟩, ⟨.privateRow 13 6, 310270699200⟩, ⟨.privateRow 13 7, 556016076000⟩, ⟨.privateRow 14 2, 1338557220⟩, ⟨.privateRow 14 3, 55489281120⟩, ⟨.privateRow 14 4, 154201791744⟩, ⟨.privateRow 14 5, 53542288800⟩, ⟨.privateRow 15 1, 22904201320⟩, ⟨.privateRow 15 2, 34072365600⟩, ⟨.privateRow 16 0, 7808250450⟩, ⟨.hall 8 13, 62162100⟩, ⟨.hall 8 14, 45750384680⟩, ⟨.hall 9 14, 65056505514⟩, ⟨.hall 7 16, 91900448640⟩, ⟨.hall 10 16, 7785678700800⟩, ⟨.hall 7 17, 1253046114320⟩, ⟨.hall 6 18, 2967450520320⟩, ⟨.hall 5 19, 4321766666880⟩, ⟨.hall 4 20, 5128680098880⟩, ⟨.hall 3 22, 51506517862800⟩, ⟨.assumptionRow 16, 170096757600⟩]
  caps := #[0, 0, 278072059933360, 0, 17505445391280, 0, 0, 423578995840, 0, 0, 183023824984, 0, 104973858055, 32374092520, 94635087092, 170096757600, 332186912750, 188434400000, 0, 0, 0, 0, 0, 0] }

theorem case_50_27_16_checked :
    (Witness.linear .conditional case_50_27_16).check 50 27 16 = true := by
  change case_50_27_16.check 50 27 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_27_17 : Certificate := {
  objectiveScale := 464508000000
  eta := 251681900036767200
  rows := #[⟨.count 2, 66461454122263200⟩, ⟨.count 3, 18210749724367200⟩, ⟨.count 4, 5074106333456160⟩, ⟨.count 5, 1433594782620000⟩, ⟨.count 6, 412329166048800⟩, ⟨.count 7, 119185134868800⟩, ⟨.count 8, 35980418073600⟩, ⟨.count 9, 11468758260960⟩, ⟨.count 10, 3855044793600⟩, ⟨.count 11, 1223235367200⟩, ⟨.count 12, 611617683600⟩, ⟨.count 13, 240940299600⟩, ⟨.count 14, 337316419440⟩, ⟨.path 12, 94531600800⟩, ⟨.privateRow 6 17, 8191970186400⟩, ⟨.privateRow 7 15, 2114920407600⟩, ⟨.privateRow 7 16, 30968859841920⟩, ⟨.privateRow 8 13, 351371270250⟩, ⟨.privateRow 8 14, 9803258439975⟩, ⟨.privateRow 8 15, 30681739318230⟩, ⟨.privateRow 9 12, 2934117426240⟩, ⟨.privateRow 9 13, 10712919617400⟩, ⟨.privateRow 9 14, 22960004283216⟩, ⟨.privateRow 9 15, 758961943740⟩, ⟨.privateRow 10 10, 767997204975⟩, ⟨.privateRow 10 11, 3724248630960⟩, ⟨.privateRow 10 12, 9091480638240⟩, ⟨.privateRow 10 13, 16003254699432⟩, ⟨.privateRow 10 14, 11559110873310⟩, ⟨.privateRow 11 8, 181220054400⟩, ⟨.privateRow 11 9, 1227868834500⟩, ⟨.privateRow 11 10, 3558502886400⟩, ⟨.privateRow 11 11, 6974912775600⟩, ⟨.privateRow 11 12, 10512410610240⟩, ⟨.privateRow 11 13, 9253034198100⟩, ⟨.privateRow 12 6, 20387256120⟩, ⟨.privateRow 12 7, 392643451200⟩, ⟨.privateRow 12 8, 1376139788100⟩, ⟨.privateRow 12 9, 3079931906700⟩, ⟨.privateRow 12 10, 5147782170300⟩, ⟨.privateRow 12 11, 6731192395620⟩, ⟨.privateRow 12 12, 344034947025⟩, ⟨.privateRow 13 5, 87109185240⟩, ⟨.privateRow 13 6, 535422888000⟩, ⟨.privateRow 13 7, 986928534900⟩, ⟨.privateRow 13 8, 3410231932800⟩, ⟨.privateRow 13 9, 880358787000⟩, ⟨.privateRow 14 3, 2190366360⟩, ⟨.privateRow 14 4, 180705224700⟩, ⟨.privateRow 14 5, 634476122280⟩, ⟨.privateRow 14 6, 1060137318240⟩, ⟨.privateRow 15 2, 30665129040⟩, ⟨.privateRow 15 3, 277349055984⟩, ⟨.privateRow 15 4, 233206413440⟩, ⟨.privateRow 16 1, 102217096800⟩, ⟨.privateRow 16 2, 28109701620⟩, ⟨.privateRow 17 0, 29204884800⟩, ⟨.hall 9 13, 39526807320⟩, ⟨.hall 8 14, 165380194980⟩, ⟨.hall 9 14, 139583959515⟩, ⟨.hall 10 14, 34723749060⟩, ⟨.hall 10 15, 2528101525950⟩, ⟨.hall 7 17, 5740954499280⟩, ⟨.hall 6 18, 8977632824160⟩, ⟨.hall 5 19, 12601803488040⟩, ⟨.hall 4 20, 14952465665280⟩, ⟨.hall 3 22, 159876983366100⟩, ⟨.hall 2 24, 2614876883498880⟩, ⟨.assumptionRow 17, 220270391880⟩]
  caps := #[0, 0, 346843220460000, 0, 0, 7858581395280, 0, 355369477320, 476293136865, 137533226040, 0, 37680265200, 67184470275, 0, 99554854620, 315629361376, 220270391880, 0, 464508000000, 0, 0, 0, 0, 0] }

theorem case_50_27_17_checked :
    (Witness.linear .conditional case_50_27_17).check 50 27 17 = true := by
  change case_50_27_17.check 50 27 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_28_1_checked :
    (Witness.rising).check 50 28 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_28_2_checked :
    (Witness.rising).check 50 28 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_28_3_checked :
    (Witness.rising).check 50 28 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_28_4_checked :
    (Witness.rising).check 50 28 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_28_5_checked :
    (Witness.rising).check 50 28 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_28_6_checked :
    (Witness.rising).check 50 28 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_28_7_checked :
    (Witness.rising).check 50 28 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_28_8_checked :
    (Witness.rising).check 50 28 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_28_9_checked :
    (Witness.rising).check 50 28 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_28_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_28_10_checked :
    (Witness.linear .positive case_50_28_10).check 50 28 10 = true := by
  change case_50_28_10.check 50 28 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_28_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_28_11_checked :
    (Witness.linear .positive case_50_28_11).check 50 28 11 = true := by
  change case_50_28_11.check 50 28 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_28_12 : Certificate := {
  objectiveScale := 1641057600000
  eta := 1388063812323988800
  rows := #[⟨.count 2, 285976217893766400⟩, ⟨.count 3, 43705799338481280⟩, ⟨.count 4, 7497291114593280⟩, ⟨.count 5, 1348944424027200⟩, ⟨.count 6, 267283105689600⟩, ⟨.count 7, 58468179369600⟩, ⟨.count 8, 15591514498560⟩, ⟨.count 9, 5011558231680⟩, ⟨.count 10, 1927522396800⟩, ⟨.count 11, 1766895530400⟩, ⟨.path 12, 206966323200⟩, ⟨.path 13, 359295081600⟩, ⟨.privateRow 5 19, 32185340643456⟩, ⟨.privateRow 5 20, 95846051180880⟩, ⟨.privateRow 6 16, 12131152862400⟩, ⟨.privateRow 6 17, 25521824328000⟩, ⟨.privateRow 6 18, 36473007130560⟩, ⟨.privateRow 6 19, 57076079860800⟩, ⟨.privateRow 7 13, 3480248772000⟩, ⟨.privateRow 7 14, 7373777085675⟩, ⟨.privateRow 7 15, 11261090669400⟩, ⟨.privateRow 7 16, 14617044842400⟩, ⟨.privateRow 7 17, 19002158295120⟩, ⟨.privateRow 7 18, 18923852697750⟩, ⟨.privateRow 8 10, 908028543240⟩, ⟨.privateRow 8 11, 2216918467764⟩, ⟨.privateRow 8 12, 3545986804360⟩, ⟨.privateRow 8 13, 4293756922455⟩, ⟨.privateRow 8 14, 6229645301880⟩, ⟨.privateRow 8 15, 6334052765040⟩, ⟨.privateRow 8 16, 292340896848⟩, ⟨.privateRow 9 7, 224877612960⟩, ⟨.privateRow 9 8, 696049754400⟩, ⟨.privateRow 9 9, 1164301407360⟩, ⟨.privateRow 9 10, 1614835430208⟩, ⟨.privateRow 9 11, 1933471540000⟩, ⟨.privateRow 10 4, 44975522592⟩, ⟨.privateRow 10 5, 82608102720⟩, ⟨.privateRow 10 6, 726527672640⟩, ⟨.privateRow 10 7, 305191046160⟩, ⟨.privateRow 11 2, 95372201925⟩, ⟨.privateRow 11 3, 107084577600⟩, ⟨.privateRow 12 0, 42518876400⟩, ⟨.privateRow 13 0, 24094029960⟩, ⟨.hall 5 19, 104898746160⟩, ⟨.hall 5 20, 467701416000⟩, ⟨.hall 6 21, 35688369225600⟩, ⟨.hall 4 22, 33646439867040⟩, ⟨.hall 3 24, 971239985299584⟩]
  caps := #[0, 4769712580651200, 48765667641600, 138838724344320, 11990617102464, 50644580130144, 407754547200, 5441592980070, 0, 0, 17757721008, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_28_12_checked :
    (Witness.linear .positive case_50_28_12).check 50 28 12 = true := by
  change case_50_28_12.check 50 28 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_28_13 : Certificate := {
  objectiveScale := 133952000000
  eta := 156892613009932800
  rows := #[⟨.count 2, 32374666176652800⟩, ⟨.count 3, 6039120421414080⟩, ⟨.count 4, 1179643706841600⟩, ⟨.count 5, 243938667772800⟩, ⟨.count 6, 52685612179200⟩, ⟨.count 7, 12368268712800⟩, ⟨.count 8, 2998368172800⟩, ⟨.count 9, 963761198400⟩, ⟨.count 10, 296541907200⟩, ⟨.count 11, 135915040800⟩, ⟨.count 12, 148270953600⟩, ⟨.path 14, 36838139520⟩, ⟨.privateRow 9 13, 648626584320⟩, ⟨.privateRow 10 13, 175453961760⟩, ⟨.privateRow 10 15, 255767394960⟩, ⟨.privateRow 11 10, 3088978200⟩, ⟨.privateRow 12 3, 3530260800⟩, ⟨.privateRow 12 14, 20593188000⟩, ⟨.privateRow 13 0, 2780080380⟩, ⟨.privateRow 14 0, 2855588736⟩, ⟨.privateRow 16 0, 6177956400⟩, ⟨.hall 14 1, 2677114440⟩, ⟨.hall 12 3, 52953912⟩, ⟨.hall 16 3, 973496160⟩, ⟨.hall 11 4, 145363680⟩, ⟨.hall 10 5, 220641300⟩, ⟨.hall 9 7, 93721320⟩, ⟨.hall 8 10, 103215168⟩, ⟨.hall 7 13, 496951455⟩, ⟨.hall 6 15, 1414389600⟩, ⟨.hall 5 18, 17723422080⟩]
  caps := #[0, 0, 0, 0, 1779118315520, 2427250425600, 473912799360, 0, 96035546880, 158373918144, 8200232320, 0, 0, 30733347040, 0, 40156716600, 92669346000, 0, 0, 0, 0, 0, 0] }

theorem case_50_28_13_checked :
    (Witness.linear .positive case_50_28_13).check 50 28 13 = true := by
  change case_50_28_13.check 50 28 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_28_14 : Certificate := {
  objectiveScale := 46644000000
  eta := 61376971293237600
  rows := #[⟨.count 2, 13939092381614400⟩, ⟨.count 3, 3304913838866640⟩, ⟨.count 4, 780967824436800⟩, ⟨.count 5, 181436969313600⟩, ⟨.count 6, 46635333544800⟩, ⟨.count 7, 11876348934450⟩, ⟨.count 8, 3085820577840⟩, ⟨.count 9, 939667168440⟩, ⟨.count 10, 321253732800⟩, ⟨.count 11, 73620647100⟩, ⟨.count 12, 80313433200⟩, ⟨.path 15, 9329266440⟩, ⟨.privateRow 14 0, 773388616⟩, ⟨.privateRow 15 0, 1450103655⟩, ⟨.privateRow 17 1, 10546208400⟩, ⟨.hall 15 1, 3346393050⟩, ⟨.hall 13 3, 25496328⟩, ⟨.hall 12 4, 30889782⟩, ⟨.hall 11 6, 416406375⟩, ⟨.hall 10 7, 271639200⟩, ⟨.hall 9 9, 149076018⟩, ⟨.hall 13 9, 3476772⟩, ⟨.hall 8 12, 62530468⟩, ⟨.hall 4 21, 1316579486040⟩]
  caps := #[0, 1005674380214400, 0, 0, 6886975405440, 9943567920, 57644987400, 130416973830, 0, 0, 0, 32700247125, 0, 91640184090, 9607207272, 29630717610, 53542288800, 0, 0, 0, 0, 0, 0] }

theorem case_50_28_14_checked :
    (Witness.linear .positive case_50_28_14).check 50 28 14 = true := by
  change case_50_28_14.check 50 28 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_28_15 : Certificate := {
  objectiveScale := 1005644640000
  eta := 1699669974274272000
  rows := #[⟨.count 2, 377704438727616000⟩, ⟨.count 3, 93077165257876800⟩, ⟨.count 4, 23216043508257600⟩, ⟨.count 5, 5679765995904000⟩, ⟨.count 6, 1566111947400000⟩, ⟨.count 7, 447646998298500⟩, ⟨.count 8, 131553403581600⟩, ⟨.count 9, 40718910632400⟩, ⟨.count 10, 14456417976000⟩, ⟨.count 11, 4417238826000⟩, ⟨.count 12, 2409402996000⟩, ⟨.count 13, 3132223894800⟩, ⟨.path 13, 251467944000⟩, ⟨.privateRow 3 25, 6744722120136000⟩, ⟨.privateRow 5 20, 464439198623400⟩, ⟨.privateRow 6 18, 210903075583200⟩, ⟨.privateRow 6 19, 513336693870000⟩, ⟨.privateRow 7 15, 11186513910000⟩, ⟨.privateRow 7 16, 75912926339250⟩, ⟨.privateRow 7 17, 202811497188300⟩, ⟨.privateRow 7 18, 334430155434375⟩, ⟨.privateRow 8 13, 7917565956300⟩, ⟨.privateRow 8 14, 31148226509400⟩, ⟨.privateRow 8 15, 76739485422600⟩, ⟨.privateRow 8 16, 132649681944780⟩, ⟨.privateRow 8 17, 175404538108800⟩, ⟨.privateRow 8 18, 14211015819000⟩, ⟨.privateRow 9 11, 4137629095600⟩, ⟨.privateRow 9 12, 13442460881850⟩, ⟨.privateRow 9 13, 31371956787600⟩, ⟨.privateRow 9 14, 53189802065400⟩, ⟨.privateRow 9 15, 72876409285680⟩, ⟨.privateRow 9 16, 78218591150700⟩, ⟨.privateRow 10 9, 1951616426760⟩, ⟨.privateRow 10 10, 5969965201200⟩, ⟨.privateRow 10 11, 13673362002300⟩, ⟨.privateRow 10 12, 23095848718800⟩, ⟨.privateRow 10 13, 31844276263800⟩, ⟨.privateRow 10 14, 23515773240960⟩, ⟨.privateRow 11 7, 894399597000⟩, ⟨.privateRow 11 8, 2750735087100⟩, ⟨.privateRow 11 9, 6358146795000⟩, ⟨.privateRow 11 10, 10917607325625⟩, ⟨.privateRow 11 11, 9350778294000⟩, ⟨.privateRow 12 5, 418299131250⟩, ⟨.privateRow 12 6, 1332472869000⟩, ⟨.privateRow 12 7, 3152302253100⟩, ⟨.privateRow 12 8, 3413320911000⟩, ⟨.privateRow 13 3, 222406430400⟩, ⟨.privateRow 13 4, 702742540500⟩, ⟨.privateRow 13 5, 1051375852800⟩, ⟨.privateRow 14 1, 124294599000⟩, ⟨.privateRow 14 2, 267711444000⟩, ⟨.privateRow 15 0, 87006219300⟩, ⟨.privateRow 16 0, 100391791500⟩, ⟨.hall 7 18, 4460213557800⟩, ⟨.hall 8 19, 137400221518560⟩, ⟨.hall 6 20, 119955587544000⟩, ⟨.hall 5 21, 251974137870000⟩, ⟨.hall 4 22, 430998547379400⟩, ⟨.hall 3 23, 515971242190404⟩, ⟨.hall 2 25, 2594123892360000⟩, ⟨.assumptionRow 15, 1377104628900⟩]
  caps := #[0, 0, 0, 915814078779600, 0, 21229058978400, 47828201421000, 865951791900, 6265418346460, 1236548393600, 0, 1013596223250, 275677962000, 0, 1287828012900, 2773065094800, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_28_15_checked :
    (Witness.linear .conditional case_50_28_15).check 50 28 15 = true := by
  change case_50_28_15.check 50 28 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_28_16 : Certificate := {
  objectiveScale := 29752800000
  eta := 27238300869780000
  rows := #[⟨.count 2, 7090605305784000⟩, ⟨.count 3, 1841827963575600⟩, ⟨.count 4, 480595584268800⟩, ⟨.count 5, 130464710376000⟩, ⟨.count 6, 37479602160000⟩, ⟨.count 7, 11009633134500⟩, ⟨.count 8, 3373164194400⟩, ⟨.count 9, 1044074631600⟩, ⟨.count 10, 370677384000⟩, ⟨.count 11, 169893801000⟩, ⟨.count 12, 61779564000⟩, ⟨.path 12, 5624892000⟩, ⟨.privateRow 2 26, 259412389236000⟩, ⟨.privateRow 5 20, 18128526616200⟩, ⟨.privateRow 6 18, 6460769515200⟩, ⟨.privateRow 6 19, 18226687479000⟩, ⟨.privateRow 7 15, 76488984000⟩, ⟨.privateRow 7 16, 2180732804250⟩, ⟨.privateRow 7 17, 6625858239000⟩, ⟨.privateRow 7 18, 12523875989625⟩, ⟨.privateRow 8 13, 42945377475⟩, ⟨.privateRow 8 14, 769670401500⟩, ⟨.privateRow 8 15, 2415352139200⟩, ⟨.privateRow 8 16, 4800512376660⟩, ⟨.privateRow 8 17, 7316330671650⟩, ⟨.privateRow 8 18, 2509051144600⟩, ⟨.privateRow 9 11, 14872858000⟩, ⟨.privateRow 9 12, 276635158800⟩, ⟨.privateRow 9 13, 911493726000⟩, ⟨.privateRow 9 14, 1891827537600⟩, ⟨.privateRow 9 15, 3009076630560⟩, ⟨.privateRow 9 16, 3837197364000⟩, ⟨.privateRow 9 17, 2403453852800⟩, ⟨.privateRow 10 9, 1853386920⟩, ⟨.privateRow 10 10, 100220181600⟩, ⟨.privateRow 10 11, 356004737550⟩, ⟨.privateRow 10 12, 780187636800⟩, ⟨.privateRow 10 13, 1297370844000⟩, ⟨.privateRow 10 14, 1736005748400⟩, ⟨.privateRow 10 15, 1760717574000⟩, ⟨.privateRow 11 8, 33463930500⟩, ⟨.privateRow 11 9, 143008250000⟩, ⟨.privateRow 11 10, 337856990625⟩, ⟨.privateRow 11 11, 597937923000⟩, ⟨.privateRow 11 12, 849469005000⟩, ⟨.privateRow 11 13, 72076158000⟩, ⟨.privateRow 12 6, 10764621000⟩, ⟨.privateRow 12 7, 57146096700⟩, ⟨.privateRow 12 8, 84660884000⟩, ⟨.privateRow 12 9, 433744022250⟩, ⟨.privateRow 12 10, 70605216000⟩, ⟨.privateRow 13 4, 3088978200⟩, ⟨.privateRow 13 5, 23588560800⟩, ⟨.privateRow 13 6, 71664294240⟩, ⟨.privateRow 13 7, 92669346000⟩, ⟨.privateRow 14 3, 10411000600⟩, ⟨.privateRow 14 4, 34883612400⟩, ⟨.privateRow 14 5, 1784742960⟩, ⟨.privateRow 15 1, 3603807900⟩, ⟨.privateRow 15 2, 6506875375⟩, ⟨.privateRow 16 0, 2574148500⟩, ⟨.hall 7 18, 226439263050⟩, ⟨.hall 8 19, 9501079147560⟩, ⟨.hall 6 20, 5456214192000⟩, ⟨.hall 5 21, 10388367990000⟩, ⟨.hall 4 22, 17205116128200⟩, ⟨.hall 3 23, 23347115031240⟩, ⟨.hall 2 25, 518824778472000⟩, ⟨.assumptionRow 16, 28965144208⟩]
  caps := #[0, 331945208460320, 66844572995200, 0, 3467325402464, 0, 99875767992, 126458217730, 62451747995, 66690231192, 5766068262, 10374703186, 987960624, 28965144208, 132697556264, 88167240854, 0, 29752800000, 0, 0, 0, 0, 0] }

theorem case_50_28_16_checked :
    (Witness.linear .conditional case_50_28_16).check 50 28 16 = true := by
  change case_50_28_16.check 50 28 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_28_17 : Certificate := {
  objectiveScale := 47817000000
  eta := 38133621217692000
  rows := #[⟨.count 2, 9684729198144000⟩, ⟨.count 3, 2464417697742000⟩, ⟨.count 4, 633512361081600⟩, ⟨.count 5, 168390498276000⟩, ⟨.count 6, 45510945480000⟩, ⟨.count 7, 12649365729000⟩, ⟨.count 8, 3747960216000⟩, ⟨.count 9, 1124388064800⟩, ⟨.count 10, 370677384000⟩, ⟨.count 11, 113262534000⟩, ⟨.count 12, 61779564000⟩, ⟨.count 13, 80313433200⟩, ⟨.path 11, 13645424000⟩, ⟨.privateRow 2 26, 778237167708000⟩, ⟨.privateRow 5 20, 30644036623200⟩, ⟨.privateRow 6 17, 193347154000⟩, ⟨.privateRow 6 18, 9566222265600⟩, ⟨.privateRow 6 19, 29894444580000⟩, ⟨.privateRow 7 15, 57366738000⟩, ⟨.privateRow 7 16, 3011753745000⟩, ⟨.privateRow 7 17, 10132878155400⟩, ⟨.privateRow 7 18, 21425281502625⟩, ⟨.privateRow 8 14, 919142624400⟩, ⟨.privateRow 8 15, 3469465949950⟩, ⟨.privateRow 8 16, 7842606751980⟩, ⟨.privateRow 8 17, 13598068158675⟩, ⟨.privateRow 8 18, 11197031145300⟩, ⟨.privateRow 9 12, 249864014400⟩, ⟨.privateRow 9 13, 1184304435600⟩, ⟨.privateRow 9 14, 2940364026600⟩, ⟨.privateRow 9 15, 5402416939920⟩, ⟨.privateRow 9 16, 7964415459000⟩, ⟨.privateRow 9 17, 7189539557200⟩, ⟨.privateRow 10 10, 61779564000⟩, ⟨.privateRow 10 11, 389211253200⟩, ⟨.privateRow 10 12, 1121740369200⟩, ⟨.privateRow 10 13, 2231271919800⟩, ⟨.privateRow 10 14, 3500430096240⟩, ⟨.privateRow 10 15, 4384804554900⟩, ⟨.privateRow 10 16, 3496723322400⟩, ⟨.privateRow 11 8, 9781764300⟩, ⟨.privateRow 11 9, 123559128000⟩, ⟨.privateRow 11 10, 426665113875⟩, ⟨.privateRow 11 11, 957583242000⟩, ⟨.privateRow 11 12, 1626861852000⟩, ⟨.privateRow 11 13, 2218916007000⟩, ⟨.privateRow 11 14, 728484025500⟩, ⟨.privateRow 12 7, 32434271100⟩, ⟨.privateRow 12 8, 161885339000⟩, ⟨.privateRow 12 9, 419586205500⟩, ⟨.privateRow 12 10, 799456977000⟩, ⟨.privateRow 12 11, 776534797500⟩, ⟨.privateRow 13 5, 4493059200⟩, ⟨.privateRow 13 6, 56219403240⟩, ⟨.privateRow 13 7, 108457456800⟩, ⟨.privateRow 13 8, 568371988800⟩, ⟨.privateRow 13 9, 5295391200⟩, ⟨.privateRow 14 4, 14602442400⟩, ⟨.privateRow 14 5, 80313433200⟩, ⟨.privateRow 14 6, 136830293600⟩, ⟨.privateRow 15 2, 2602750150⟩, ⟨.privateRow 15 3, 29813319900⟩, ⟨.privateRow 15 4, 31233001800⟩, ⟨.privateRow 16 1, 11154643500⟩, ⟨.privateRow 16 2, 3042175500⟩, ⟨.hall 8 17, 164055451560⟩, ⟨.hall 7 18, 229668238800⟩, ⟨.hall 8 18, 78575657160⟩, ⟨.hall 9 18, 3343575034800⟩, ⟨.hall 7 19, 2256584380050⟩, ⟨.hall 6 20, 11174345208000⟩, ⟨.hall 5 21, 19685432676000⟩, ⟨.hall 4 22, 31283828175600⟩, ⟨.hall 3 23, 42846279622146⟩, ⟨.hall 2 25, 1017694757772000⟩, ⟨.assumptionRow 17, 29446346160⟩]
  caps := #[0, 1263649533260400, 59142132306400, 0, 0, 1120955866800, 185907802080, 106902802890, 50196798535, 45084742040, 43066596060, 38869369670, 48571987420, 0, 72079236320, 29446346160, 29446346160, 448723653840, 47817000000, 0, 0, 0, 0] }

theorem case_50_28_17_checked :
    (Witness.linear .conditional case_50_28_17).check 50 28 17 = true := by
  change case_50_28_17.check 50 28 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_28_18 : Certificate := {
  objectiveScale := 107640000000
  eta := 108953203479120000
  rows := #[⟨.count 2, 26978888480544000⟩, ⟨.count 3, 7004134509372000⟩, ⟨.count 4, 1835001321753600⟩, ⟨.count 5, 491518211184000⟩, ⟨.count 6, 133320299112000⟩, ⟨.count 7, 35839869565500⟩, ⟨.count 8, 9744696561600⟩, ⟨.count 9, 2650343295600⟩, ⟨.count 10, 741354768000⟩, ⟨.count 11, 169893801000⟩, ⟨.path 11, 16590912000⟩, ⟨.path 12, 24170328000⟩, ⟨.privateRow 2 26, 2594123892360000⟩, ⟨.privateRow 5 20, 91932109869600⟩, ⟨.privateRow 6 17, 446185740000⟩, ⟨.privateRow 6 18, 28056159331200⟩, ⟨.privateRow 6 19, 90419540211000⟩, ⟨.privateRow 7 15, 200783583000⟩, ⟨.privateRow 7 16, 8600230138500⟩, ⟨.privateRow 7 17, 29916753867000⟩, ⟨.privateRow 7 18, 65882113171875⟩, ⟨.privateRow 8 13, 35137127025⟩, ⟨.privateRow 8 14, 2596801006800⟩, ⟨.privateRow 8 15, 9939902822850⟩, ⟨.privateRow 8 16, 23490340653780⟩, ⟨.privateRow 8 17, 43160104362375⟩, ⟨.privateRow 8 18, 42195785431800⟩, ⟨.privateRow 9 12, 742899257100⟩, ⟨.privateRow 9 13, 3285201862800⟩, ⟨.privateRow 9 14, 8504300204400⟩, ⟨.privateRow 9 15, 16619526443520⟩, ⟨.privateRow 9 16, 26483354597700⟩, ⟨.privateRow 9 17, 28457726497200⟩, ⟨.privateRow 10 10, 193575967200⟩, ⟨.privateRow 10 11, 1058747278050⟩, ⟨.privateRow 10 12, 3113690025600⟩, ⟨.privateRow 10 13, 6613502326200⟩, ⟨.privateRow 10 14, 11227817961360⟩, ⟨.privateRow 10 15, 15508215053100⟩, ⟨.privateRow 10 16, 14685002362800⟩, ⟨.privateRow 11 8, 44790183900⟩, ⟨.privateRow 11 9, 322626612000⟩, ⟨.privateRow 11 10, 1135199488500⟩, ⟨.privateRow 11 11, 2709475164000⟩, ⟨.privateRow 11 12, 5006718832500⟩, ⟨.privateRow 11 13, 7515483960600⟩, ⟨.privateRow 11 14, 8583498173250⟩, ⟨.privateRow 12 6, 7020405000⟩, ⟨.privateRow 12 7, 89580367800⟩, ⟨.privateRow 12 8, 401567166000⟩, ⟨.privateRow 12 9, 1129407654375⟩, ⟨.privateRow 12 10, 2341004193000⟩, ⟨.privateRow 12 11, 3881815938000⟩, ⟨.privateRow 12 12, 1887365680200⟩, ⟨.privateRow 13 5, 18533869200⟩, ⟨.privateRow 13 6, 133443858240⟩, ⟨.privateRow 13 7, 467465367600⟩, ⟨.privateRow 13 8, 1132882754850⟩, ⟨.privateRow 13 9, 1832205355200⟩, ⟨.privateRow 14 4, 36506106000⟩, ⟨.privateRow 14 5, 184720896360⟩, ⟨.privateRow 14 6, 556244889200⟩, ⟨.privateRow 14 7, 491919778350⟩, ⟨.privateRow 15 3, 63885685500⟩, ⟨.privateRow 15 4, 267042165390⟩, ⟨.privateRow 15 5, 78082504500⟩, ⟨.privateRow 16 2, 109518318000⟩, ⟨.privateRow 17 1, 24337404000⟩, ⟨.hall 8 18, 4220400464280⟩, ⟨.hall 9 18, 25932784878000⟩, ⟨.hall 7 19, 1711680045075⟩, ⟨.hall 8 19, 35436963842280⟩, ⟨.hall 6 20, 37646487216000⟩, ⟨.hall 7 20, 276244746277500⟩, ⟨.hall 5 21, 64111071024000⟩, ⟨.hall 4 22, 99787694806800⟩, ⟨.hall 3 23, 135672679570428⟩, ⟨.hall 2 25, 3272587064208000⟩]
  caps := #[0, 0, 311169185184000, 0, 0, 887454672000, 0, 146345647500, 21919311375, 102408393750, 0, 26738662500, 54248644125, 20680401240, 192248559230, 0, 550379466000, 574463916000, 968760000000, 107640000000, 0, 0, 0] }

theorem case_50_28_18_checked :
    (Witness.linear .negative case_50_28_18).check 50 28 18 = true := by
  change case_50_28_18.check 50 28 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_29_1_checked :
    (Witness.rising).check 50 29 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_29_2_checked :
    (Witness.rising).check 50 29 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_29_3_checked :
    (Witness.rising).check 50 29 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_29_4_checked :
    (Witness.rising).check 50 29 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_29_5_checked :
    (Witness.rising).check 50 29 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_29_6_checked :
    (Witness.rising).check 50 29 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_29_7_checked :
    (Witness.rising).check 50 29 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_29_8_checked :
    (Witness.rising).check 50 29 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_29_9_checked :
    (Witness.rising).check 50 29 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_29_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_29_10_checked :
    (Witness.linear .positive case_50_29_10).check 50 29 10 = true := by
  change case_50_29_10.check 50 29 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_29_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_29_11_checked :
    (Witness.linear .positive case_50_29_11).check 50 29 11 = true := by
  change case_50_29_11.check 50 29 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_29_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_29_12_checked :
    (Witness.linear .positive case_50_29_12).check 50 29 12 = true := by
  change case_50_29_12.check 50 29 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_29_13 : Certificate := {
  objectiveScale := 160888000000
  eta := 339933994854854400
  rows := #[⟨.count 2, 69807873943407600⟩, ⟨.count 3, 14376907677132000⟩, ⟨.count 4, 3067073637788160⟩, ⟨.count 5, 638973674539200⟩, ⟨.count 6, 145648411108200⟩, ⟨.count 7, 32888350895400⟩, ⟨.count 8, 8143782126480⟩, ⟨.count 9, 2168462696400⟩, ⟨.count 10, 722820898800⟩, ⟨.count 11, 361410449400⟩, ⟨.path 13, 58507394400⟩, ⟨.privateRow 8 20, 51681694264200⟩, ⟨.privateRow 10 15, 498746420172⟩, ⟨.privateRow 10 16, 2276885831220⟩, ⟨.hall 11 4, 696837141⟩, ⟨.hall 12 5, 1837812240⟩, ⟨.hall 11 6, 823511205⟩, ⟨.hall 10 7, 688564800⟩, ⟨.hall 12 7, 195745410⟩, ⟨.hall 9 8, 248457132⟩, ⟨.hall 11 13, 3382950285⟩, ⟨.hall 8 16, 15663428352⟩, ⟨.hall 9 18, 1270262621628⟩, ⟨.hall 10 18, 5915718408600⟩]
  caps := #[0, 406176670317600, 0, 0, 4141205635840, 1155497616000, 776831855800, 0, 0, 0, 0, 0, 163210608600, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_29_13_checked :
    (Witness.linear .positive case_50_29_13).check 50 29 13 = true := by
  change case_50_29_13.check 50 29 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_29_14 : Certificate := {
  objectiveScale := 21294000000
  eta := 41817277144843200
  rows := #[⟨.count 2, 9712399852995840⟩, ⟨.count 3, 2215108738402560⟩, ⟨.count 4, 549044046270720⟩, ⟨.count 5, 135033652353600⟩, ⟨.count 6, 32888350895400⟩, ⟨.count 7, 8526609491400⟩, ⟨.count 8, 2227359214080⟩, ⟨.count 9, 578256719040⟩, ⟨.count 10, 160626866400⟩, ⟨.count 11, 80313433200⟩, ⟨.path 14, 4913590500⟩, ⟨.privateRow 13 2, 1427794368⟩, ⟨.privateRow 13 4, 2471182560⟩, ⟨.privateRow 14 1, 5800414620⟩, ⟨.privateRow 14 4, 4350310965⟩, ⟨.privateRow 15 1, 17401243860⟩, ⟨.privateRow 17 10, 556839803520⟩, ⟨.hall 15 1, 43503109650⟩, ⟨.hall 12 4, 112483800⟩, ⟨.hall 10 8, 51777600⟩, ⟨.hall 8 12, 173080336⟩, ⟨.hall 11 13, 819257010⟩, ⟨.hall 6 18, 16901169480⟩]
  caps := #[0, 0, 20432224154160, 0, 1117256147280, 333689756400, 0, 0, 79234122240, 40855683960, 30792106800, 0, 59838334164, 23937774924, 0, 243617414040, 0, 0, 0, 0, 0, 0] }

theorem case_50_29_14_checked :
    (Witness.linear .positive case_50_29_14).check 50 29 14 = true := by
  change case_50_29_14.check 50 29 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_29_15 : Certificate := {
  objectiveScale := 274266720000
  eta := 674472212013600000
  rows := #[⟨.count 2, 153779664339100800⟩, ⟨.count 3, 34078595975424000⟩, ⟨.count 4, 8614311760454400⟩, ⟨.count 5, 2143833243552000⟩, ⟨.count 6, 532478062116000⟩, ⟨.count 7, 151042796704800⟩, ⟨.count 8, 44547184281600⟩, ⟨.count 9, 13492656777600⟩, ⟨.count 10, 4818805992000⟩, ⟨.count 11, 1606268664000⟩, ⟨.path 12, 12790596000⟩, ⟨.path 13, 70677152000⟩, ⟨.privateRow 2 27, 1348944424027200⟩, ⟨.privateRow 4 23, 986070485400000⟩, ⟨.privateRow 5 20, 77957572492800⟩, ⟨.privateRow 5 21, 349416976708800⟩, ⟨.privateRow 5 22, 794424786355200⟩, ⟨.privateRow 6 18, 52203731580000⟩, ⟨.privateRow 6 19, 135729702108000⟩, ⟨.privateRow 6 20, 289730710269000⟩, ⟨.privateRow 6 21, 436771220886000⟩, ⟨.privateRow 7 16, 25654405233600⟩, ⟨.privateRow 7 17, 55683980352000⟩, ⟨.privateRow 7 18, 110671910949600⟩, ⟨.privateRow 7 19, 163919717161200⟩, ⟨.privateRow 7 20, 197446113664800⟩, ⟨.privateRow 8 13, 1237421785600⟩, ⟨.privateRow 8 14, 10005715219500⟩, ⟨.privateRow 8 15, 23516538130800⟩, ⟨.privateRow 8 16, 44779200866400⟩, ⟨.privateRow 8 17, 64871837110080⟩, ⟨.privateRow 8 18, 77435535177000⟩, ⟨.privateRow 8 19, 70649050071600⟩, ⟨.privateRow 9 11, 1028011944960⟩, ⟨.privateRow 9 12, 4307179676800⟩, ⟨.privateRow 9 13, 9557298550800⟩, ⟨.privateRow 9 14, 19275223968000⟩, ⟨.privateRow 9 15, 14170859102400⟩, ⟨.privateRow 9 16, 60395701766400⟩, ⟨.privateRow 10 9, 598700138400⟩, ⟨.privateRow 10 10, 2023898516640⟩, ⟨.privateRow 10 11, 4229840815200⟩, ⟨.privateRow 10 12, 3172380611400⟩, ⟨.privateRow 10 13, 23612149360800⟩, ⟨.privateRow 10 14, 936990054000⟩, ⟨.privateRow 11 7, 316386252000⟩, ⟨.privateRow 11 8, 1022170968000⟩, ⟨.privateRow 11 9, 657109908000⟩, ⟨.privateRow 11 10, 6895597800000⟩, ⟨.privateRow 11 11, 1277713710000⟩, ⟨.privateRow 12 5, 160626866400⟩, ⟨.privateRow 12 6, 548808460200⟩, ⟨.privateRow 12 7, 1124388064800⟩, ⟨.privateRow 12 8, 819197018640⟩, ⟨.privateRow 13 3, 91786780800⟩, ⟨.privateRow 13 4, 313016457600⟩, ⟨.privateRow 13 5, 196321725600⟩, ⟨.privateRow 14 0, 21751554825⟩, ⟨.privateRow 14 1, 46403316960⟩, ⟨.privateRow 14 2, 49717839600⟩, ⟨.hall 6 21, 4766427666000⟩, ⟨.hall 7 21, 60682883133600⟩, ⟨.hall 6 22, 340459119000000⟩, ⟨.hall 5 23, 1316694118740000⟩, ⟨.hall 4 24, 2961051339197952⟩, ⟨.hall 3 25, 5439468203769600⟩, ⟨.hall 2 26, 6594839406355200⟩, ⟨.assumptionRow 15, 393449238000⟩]
  caps := #[0, 0, 62074982642400, 188381265436000, 0, 0, 3481722621000, 0, 3328528572460, 1167424119680, 270818871960, 34635146000, 1196295285640, 732643222400, 0, 3172018122000, 274266720000, 0, 0, 0, 0, 0] }

theorem case_50_29_15_checked :
    (Witness.linear .conditional case_50_29_15).check 50 29 15 = true := by
  change case_50_29_15.check 50 29 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_29_16 : Certificate := {
  objectiveScale := 1693177200000
  eta := 3561213279431808000
  rows := #[⟨.count 2, 786434599207857600⟩, ⟨.count 3, 196803891758073600⟩, ⟨.count 4, 48420005115081600⟩, ⟨.count 5, 12097344731472000⟩, ⟨.count 6, 3043477551114000⟩, ⟨.count 7, 803937466332000⟩, ⟨.count 8, 229696418952000⟩, ⟨.count 9, 63608239094400⟩, ⟨.count 10, 17668955304000⟩, ⟨.count 11, 8834477652000⟩, ⟨.path 11, 736506650880⟩, ⟨.privateRow 2 27, 51934360325047200⟩, ⟨.privateRow 4 22, 1334153366746200⟩, ⟨.privateRow 4 23, 8200162156586400⟩, ⟨.privateRow 5 20, 851408059582080⟩, ⟨.privateRow 5 21, 2886518331496800⟩, ⟨.privateRow 5 22, 6625465595548800⟩, ⟨.privateRow 6 18, 389207821002000⟩, ⟨.privateRow 6 19, 1066174211302200⟩, ⟨.privateRow 6 20, 2383100346627000⟩, ⟨.privateRow 6 21, 3837844333323000⟩, ⟨.privateRow 7 16, 156959219617200⟩, ⟨.privateRow 7 17, 405158961207000⟩, ⟨.privateRow 7 18, 889690796074080⟩, ⟨.privateRow 7 19, 1440387960511500⟩, ⟨.privateRow 7 20, 1924345554331200⟩, ⟨.privateRow 8 13, 425363738800⟩, ⟨.privateRow 8 14, 59098974459525⟩, ⟨.privateRow 8 15, 156959219617200⟩, ⟨.privateRow 8 16, 346777788056700⟩, ⟨.privateRow 8 17, 567732982176360⟩, ⟨.privateRow 8 18, 764697661427700⟩, ⟨.privateRow 8 19, 825631017010800⟩, ⟨.privateRow 9 11, 706758212160⟩, ⟨.privateRow 9 12, 21333627515200⟩, ⟨.privateRow 9 13, 61546860975600⟩, ⟨.privateRow 9 14, 141519918196800⟩, ⟨.privateRow 9 15, 238334574878400⟩, ⟨.privateRow 9 16, 327700224371520⟩, ⟨.privateRow 9 17, 365158409616000⟩, ⟨.privateRow 9 18, 149989798358400⟩, ⟨.privateRow 10 9, 240940299600⟩, ⟨.privateRow 10 10, 7951029886800⟩, ⟨.privateRow 10 11, 24442054837200⟩, ⟨.privateRow 10 12, 60184879004250⟩, ⟨.privateRow 10 13, 73199957688000⟩, ⟨.privateRow 10 14, 221892630359400⟩, ⟨.privateRow 10 15, 62371412223120⟩, ⟨.privateRow 11 8, 2920488480000⟩, ⟨.privateRow 11 9, 10199806016400⟩, ⟨.privateRow 11 10, 26681907252000⟩, ⟨.privateRow 11 11, 51701772622500⟩, ⟨.privateRow 11 12, 58055138856000⟩, ⟨.privateRow 12 6, 957068412300⟩, ⟨.privateRow 12 7, 4336925392800⟩, ⟨.privateRow 12 8, 12633303042360⟩, ⟨.privateRow 12 9, 26503432956000⟩, ⟨.privateRow 12 10, 1546033589100⟩, ⟨.privateRow 13 4, 271830081600⟩, ⟨.privateRow 13 5, 1766895530400⟩, ⟨.privateRow 13 6, 6317990078400⟩, ⟨.privateRow 13 7, 4593928379040⟩, ⟨.privateRow 14 3, 883447765200⟩, ⟨.privateRow 14 4, 2233159628700⟩, ⟨.privateRow 15 1, 273448117800⟩, ⟨.privateRow 15 2, 294482588400⟩, ⟨.hall 7 21, 1315534035816000⟩, ⟨.hall 6 22, 5110745321682000⟩, ⟨.hall 5 23, 12945945390378000⟩, ⟨.hall 4 24, 27094377055794048⟩, ⟨.hall 3 25, 49200972939518400⟩, ⟨.hall 2 26, 71444093568848000⟩, ⟨.assumptionRow 16, 1751480987256⟩]
  caps := #[0, 0, 14198520068647200, 0, 405274969499400, 71484713283984, 94762533729864, 1489398862380, 11885659020235, 1657326219120, 14999666851026, 0, 3561265761768, 2163001357440, 1972440611856, 1751480987256, 18566645412744, 1693177200000, 0, 0, 0, 0] }

theorem case_50_29_16_checked :
    (Witness.linear .conditional case_50_29_16).check 50 29 16 = true := by
  change case_50_29_16.check 50 29 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_29_17 : Certificate := {
  objectiveScale := 345517914772800000
  eta := 1035645781976422592976000
  rows := #[⟨.count 2, 205098478391409180177600⟩, ⟨.count 3, 44247404926546847625600⟩, ⟨.count 4, 9405245491633146355200⟩, ⟨.count 5, 1948947929415959472000⟩, ⟨.count 6, 408650372296894728000⟩, ⟨.count 7, 91684378399944330000⟩, ⟨.count 8, 23052072283414574400⟩, ⟨.count 9, 7254148620654936000⟩, ⟨.count 10, 2418049540218312000⟩, ⟨.count 11, 1209024770109156000⟩, ⟨.count 12, 1450829724130987200⟩, ⟨.path 9, 699524037031248000⟩, ⟨.privateRow 2 27, 11168729021314361296800⟩, ⟨.privateRow 4 22, 342899575215791794200⟩, ⟨.privateRow 4 23, 1775358839645398207200⟩, ⟨.privateRow 5 20, 196990435876451817600⟩, ⟨.privateRow 5 21, 603545165238490675200⟩, ⟨.privateRow 5 22, 1452979101500070144000⟩, ⟨.privateRow 6 18, 79241498474237599500⟩, ⟨.privateRow 6 19, 213231668621584813200⟩, ⟨.privateRow 6 20, 506228746451121193500⟩, ⟨.privateRow 6 21, 885409139976605244000⟩, ⟨.privateRow 7 16, 27168513762595748400⟩, ⟨.privateRow 7 17, 75967056388525302000⟩, ⟨.privateRow 7 18, 182320935332460724800⟩, ⟨.privateRow 7 19, 326003454053516339100⟩, ⟨.privateRow 7 20, 485665250152847965200⟩, ⟨.privateRow 8 14, 8349827318566358625⟩, ⟨.privateRow 8 15, 26831714005208197800⟩, ⟨.privateRow 8 16, 67802780788149306900⟩, ⟨.privateRow 8 17, 125476620724495240200⟩, ⟨.privateRow 8 18, 191620350855883649700⟩, ⟨.privateRow 8 19, 240475026774711128400⟩, ⟨.privateRow 9 12, 2274757715612782400⟩, ⟨.privateRow 9 13, 9249039491335043400⟩, ⟨.privateRow 9 14, 25838586515475676800⟩, ⟨.privateRow 9 15, 50832774778811625600⟩, ⟨.privateRow 9 16, 80569410680074155840⟩, ⟨.privateRow 9 17, 105265756650837182400⟩, ⟨.privateRow 9 18, 104459740137431078400⟩, ⟨.privateRow 10 10, 507790403445845520⟩, ⟨.privateRow 10 11, 3049429142386426800⟩, ⟨.privateRow 10 12, 9959341543774172550⟩, ⟨.privateRow 10 13, 21589728037663500000⟩, ⟨.privateRow 10 14, 36371495167450443000⟩, ⟨.privateRow 10 15, 50222888950334340240⟩, ⟨.privateRow 10 16, 35363974525692813000⟩, ⟨.privateRow 11 8, 49959701244180000⟩, ⟨.privateRow 11 9, 934246413266166000⟩, ⟨.privateRow 11 10, 3822472252971372000⟩, ⟨.privateRow 11 11, 9507331146767454000⟩, ⟨.privateRow 11 12, 17601516458342388000⟩, ⟨.privateRow 11 13, 25371201615169410000⟩, ⟨.privateRow 12 7, 186849282653233200⟩, ⟨.privateRow 12 8, 1414558981027712520⟩, ⟨.privateRow 12 9, 3815144830122225600⟩, ⟨.privateRow 12 10, 9914003114895079200⟩, ⟨.privateRow 12 11, 5164262946609109200⟩, ⟨.privateRow 13 4, 12400254052401600⟩, ⟨.privateRow 13 6, 424990525250491200⟩, ⟨.privateRow 13 7, 1902198971638405440⟩, ⟨.privateRow 13 8, 4352489172392961600⟩, ⟨.privateRow 14 4, 87318455618994600⟩, ⟨.privateRow 14 5, 714423727791774000⟩, ⟨.privateRow 14 6, 1204994687542125480⟩, ⟨.privateRow 15 3, 261955366856983800⟩, ⟨.privateRow 15 4, 285769491116709600⟩, ⟨.privateRow 16 1, 100752064175763000⟩, ⟨.hall 8 20, 70253934578025369600⟩, ⟨.hall 7 21, 530769201500768630400⟩, ⟨.hall 6 22, 1505787784876601226000⟩, ⟨.hall 5 23, 3350409142100822802000⟩, ⟨.hall 4 24, 6515270058749506838784⟩, ⟨.hall 3 25, 11370152548014546686400⟩, ⟨.hall 2 26, 16245424031002707340800⟩, ⟨.assumptionRow 17, 246244996336945320⟩]
  caps := #[0, 0, 516275557017007788000, 131349297838142696400, 0, 11580860270243473440, 1956218357034101160, 0, 1190220433281454575, 0, 1917599644305272070, 115337988727098480, 0, 237694616235443400, 4941623799856183440, 505239466618723320, 246244996336945320, 3554452066163854680, 345517914772800000, 0, 0, 0] }

theorem case_50_29_17_checked :
    (Witness.linear .conditional case_50_29_17).check 50 29 17 = true := by
  change case_50_29_17.check 50 29 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_29_18 : Certificate := {
  objectiveScale := 1062807236419500000
  eta := 3199067684398031039193600
  rows := #[⟨.count 2, 674089262069585111830080⟩, ⟨.count 3, 155142756123062407539840⟩, ⟨.count 4, 34877053702083797043840⟩, ⟨.count 5, 7663990840552558512000⟩, ⟨.count 6, 1635967275579488451600⟩, ⟨.count 7, 350774965394520947280⟩, ⟨.count 8, 70744530835869770880⟩, ⟨.count 9, 12244245721592844960⟩, ⟨.path 10, 1290005929192780800⟩, ⟨.privateRow 2 27, 48557277352470113987760⟩, ⟨.privateRow 4 22, 1027269541512525631320⟩, ⟨.privateRow 4 23, 6547799354031057682560⟩, ⟨.privateRow 5 20, 603686663132755378176⟩, ⟨.privateRow 5 21, 2172446634418167547440⟩, ⟨.privateRow 5 22, 5502352398345426624000⟩, ⟨.privateRow 6 18, 250553546710372105200⟩, ⟨.privateRow 6 19, 744291418169046547800⟩, ⟨.privateRow 6 20, 1879151600327790789000⟩, ⟨.privateRow 6 21, 3469675340474515672500⟩, ⟨.privateRow 7 16, 89272860340502329920⟩, ⟨.privateRow 7 17, 257922768672441873000⟩, ⟨.privateRow 7 18, 657334599016623287760⟩, ⟨.privateRow 7 19, 1253504655748067502780⟩, ⟨.privateRow 7 20, 1994602744400217151200⟩, ⟨.privateRow 8 13, 1064443172298966460⟩, ⟨.privateRow 8 14, 27634582357761629250⟩, ⟨.privateRow 8 15, 88851761942669771760⟩, ⟨.privateRow 8 16, 235937923152267065730⟩, ⟨.privateRow 8 17, 468682516787637232080⟩, ⟨.privateRow 8 18, 772662922723015153830⟩, ⟨.privateRow 8 19, 1059694118145632609640⟩, ⟨.privateRow 9 11, 589537756965581424⟩, ⟨.privateRow 9 12, 8263606166013278080⟩, ⟨.privateRow 9 13, 29533574171064223260⟩, ⟨.privateRow 9 14, 86422348109020397760⟩, ⟨.privateRow 9 15, 182454377604476097120⟩, ⟨.privateRow 9 16, 315175954685445453600⟩, ⟨.privateRow 9 17, 453830700217927392360⟩, ⟨.privateRow 9 18, 515014137944034849120⟩, ⟨.privateRow 10 9, 154599062141323800⟩, ⟨.privateRow 10 10, 2380825556976386520⟩, ⟨.privateRow 10 11, 9636674873475850200⟩, ⟨.privateRow 10 12, 31588453372025985435⟩, ⟨.privateRow 10 13, 73999945372959932040⟩, ⟨.privateRow 10 14, 136443978943861008420⟩, ⟨.privateRow 10 15, 122714551565297179488⟩, ⟨.privateRow 10 16, 431184514265259144390⟩, ⟨.privateRow 11 8, 562178407786632000⟩, ⟨.privateRow 11 9, 3030141617969946480⟩, ⟨.privateRow 11 10, 11577751987028026800⟩, ⟨.privateRow 11 11, 30726563600588105250⟩, ⟨.privateRow 11 12, 62723048068765656000⟩, ⟨.privateRow 11 13, 103581371634686946000⟩, ⟨.privateRow 11 14, 101293305514995353760⟩, ⟨.privateRow 12 6, 28343161392576030⟩, ⟨.privateRow 12 7, 803915123134883760⟩, ⟨.privateRow 12 8, 4183450621544222028⟩, ⟨.privateRow 12 9, 13037854240584973800⟩, ⟨.privateRow 12 10, 30185466883093471950⟩, ⟨.privateRow 12 11, 55536400237224689640⟩, ⟨.privateRow 12 12, 15872170379842576800⟩, ⟨.privateRow 13 5, 37790881856768040⟩, ⟨.privateRow 13 6, 1319245330272629760⟩, ⟨.privateRow 13 7, 5577934162058962704⟩, ⟨.privateRow 13 8, 15166740585182906720⟩, ⟨.privateRow 13 9, 21654175303928086920⟩, ⟨.privateRow 14 4, 122820366034496130⟩, ⟨.privateRow 14 5, 2143773661693023360⟩, ⟨.privateRow 14 6, 7811375279793953868⟩, ⟨.privateRow 14 7, 4912814641379845200⟩, ⟨.privateRow 15 3, 245640732068992260⟩, ⟨.privateRow 15 4, 3751603907962790880⟩, ⟨.privateRow 15 5, 589537756965581424⟩, ⟨.privateRow 16 2, 614101830172480650⟩, ⟨.privateRow 16 3, 669929269279069800⟩, ⟨.hall 8 20, 681617939958300808320⟩, ⟨.hall 7 21, 2739608753789828040120⟩, ⟨.hall 6 22, 6796665455712434101800⟩, ⟨.hall 5 23, 14116972872004985182200⟩, ⟨.hall 4 24, 26258011695246996624960⟩, ⟨.hall 3 25, 44371105787432204660880⟩, ⟨.hall 2 26, 62204093863295047984320⟩, ⟨.assumptionRow 18, 246790028476019952⟩]
  caps := #[0, 14614476188519305098000, 2690327065024560012480, 0, 0, 6772351468536925920, 3771570132588721320, 1288202702246336448, 2051013933509999458, 4338528117613344512, 1645530767822772864, 246790028476019952, 3507821554217326632, 832372735355430192, 246790028476019952, 10619508796952055000, 246790028476019952, 54676900453416780528, 10381282335718980048, 1062807236419500000, 0, 0] }

theorem case_50_29_18_checked :
    (Witness.linear .conditional case_50_29_18).check 50 29 18 = true := by
  change case_50_29_18.check 50 29 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_30_1_checked :
    (Witness.rising).check 50 30 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_30_2_checked :
    (Witness.rising).check 50 30 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_30_3_checked :
    (Witness.rising).check 50 30 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_30_4_checked :
    (Witness.rising).check 50 30 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_30_5_checked :
    (Witness.rising).check 50 30 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_30_6_checked :
    (Witness.rising).check 50 30 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_30_7_checked :
    (Witness.rising).check 50 30 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_30_8_checked :
    (Witness.rising).check 50 30 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_30_9_checked :
    (Witness.rising).check 50 30 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_30_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_30_10_checked :
    (Witness.linear .positive case_50_30_10).check 50 30 10 = true := by
  change case_50_30_10.check 50 30 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_30_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_30_11_checked :
    (Witness.linear .positive case_50_30_11).check 50 30 11 = true := by
  change case_50_30_11.check 50 30 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_30_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_30_12_checked :
    (Witness.linear .positive case_50_30_12).check 50 30 12 = true := by
  change case_50_30_12.check 50 30 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_30_13 : Certificate := {
  objectiveScale := 2229907680000
  eta := 9971397182409062400
  rows := #[⟨.count 2, 2022706665291312000⟩, ⟨.count 3, 410008107829320000⟩, ⟨.count 4, 81894429903686400⟩, ⟨.count 5, 17686624259304000⟩, ⟨.count 6, 3805304007304800⟩, ⟨.count 7, 830735381876400⟩, ⟨.count 8, 197892299404800⟩, ⟨.count 9, 49473074851200⟩, ⟨.count 10, 11243880648000⟩, ⟨.path 12, 1393657993728⟩, ⟨.privateRow 8 18, 704579041005840⟩, ⟨.privateRow 8 19, 663763754253600⟩, ⟨.privateRow 9 18, 207512063959200⟩, ⟨.privateRow 9 21, 1063671109300800⟩, ⟨.privateRow 10 10, 15434781616800⟩, ⟨.privateRow 11 18, 109627836318000⟩, ⟨.privateRow 12 15, 39509747277000⟩, ⟨.privateRow 13 13, 1236826871280⟩, ⟨.hall 13 1, 225192567600⟩, ⟨.hall 14 1, 558289907175⟩, ⟨.hall 12 2, 26946119200⟩, ⟨.hall 13 3, 5629814190⟩, ⟨.hall 14 3, 15951140205⟩, ⟨.hall 12 4, 2694611920⟩, ⟨.hall 15 4, 78528690240⟩, ⟨.hall 16 4, 321253732800⟩, ⟨.hall 13 6, 2474643600⟩, ⟨.hall 14 6, 5577321750⟩, ⟨.hall 15 8, 4164400240⟩, ⟨.hall 9 9, 6365399040⟩, ⟨.hall 10 12, 18509960700⟩, ⟨.hall 11 12, 18304347600⟩, ⟨.hall 12 13, 3464501040⟩, ⟨.hall 7 14, 3224621400⟩, ⟨.hall 10 15, 15374759400⟩, ⟨.hall 11 17, 13670191735200⟩, ⟨.hall 8 18, 1974301449120⟩, ⟨.hall 9 20, 792158162796000⟩]
  caps := #[0, 3999223468880640, 0, 0, 30844083029760, 53429479975872, 0, 25643543797872, 1119756718080, 1633117405920, 3057472087488, 10795103150832, 4024168676528, 2367773908500, 5365212923070, 16748697215250, 2998368172800, 0, 0, 0, 0] }

theorem case_50_30_13_checked :
    (Witness.linear .positive case_50_30_13).check 50 30 13 = true := by
  change case_50_30_13.check 50 30 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_30_14 : Certificate := {
  objectiveScale := 442442000000
  eta := 2036568844175065200
  rows := #[⟨.count 2, 453351822085562400⟩, ⟨.count 3, 103673478693985200⟩, ⟨.count 4, 22739945476248000⟩, ⟨.count 5, 5469645976294500⟩, ⟨.count 6, 1292042356605000⟩, ⟨.count 7, 310090165585200⟩, ⟨.count 8, 79510298868000⟩, ⟨.count 9, 19877574717000⟩, ⟨.count 10, 7228208988000⟩, ⟨.path 12, 239683219776⟩, ⟨.hall 12 6, 2070134550⟩, ⟨.hall 10 10, 428396850⟩, ⟨.hall 11 10, 1353221100⟩, ⟨.hall 9 11, 4000131135⟩, ⟨.hall 12 13, 10764699660⟩, ⟨.hall 8 14, 7695667980⟩, ⟨.hall 10 17, 180705224700⟩]
  caps := #[0, 4309731264318480, 1424937589435360, 160006370764240, 23797503970240, 6879805856924, 0, 0, 0, 255815744184, 0, 1920174524268, 682125219776, 442442000000, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_30_14_checked :
    (Witness.linear .positive case_50_30_14).check 50 30 14 = true := by
  change case_50_30_14.check 50 30 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_30_15 : Certificate := {
  objectiveScale := 491891400000
  eta := 2305885598432095680
  rows := #[⟨.count 2, 478889469944645760⟩, ⟨.count 3, 108242140466940480⟩, ⟨.count 4, 23667919008814080⟩, ⟨.count 5, 5788349757590400⟩, ⟨.count 6, 1382772442091040⟩, ⟨.count 7, 353732485186080⟩, ⟨.count 8, 98946149702400⟩, ⟨.count 9, 29683844910720⟩, ⟨.count 10, 6746328388800⟩, ⟨.path 12, 257708715264⟩, ⟨.privateRow 2 28, 13120259450538240⟩, ⟨.privateRow 3 26, 10204646239307520⟩, ⟨.privateRow 4 23, 1238063698151280⟩, ⟨.privateRow 4 24, 3880338170829120⟩, ⟨.privateRow 5 20, 10719166217760⟩, ⟨.privateRow 5 21, 797505966601344⟩, ⟨.privateRow 5 22, 1479244938050880⟩, ⟨.privateRow 5 23, 2808421549053120⟩, ⟨.privateRow 6 18, 71971544604960⟩, ⟨.privateRow 6 19, 311749084166520⟩, ⟨.privateRow 6 20, 599201391572784⟩, ⟨.privateRow 6 21, 1039759123122720⟩, ⟨.privateRow 6 22, 1364907165061440⟩, ⟨.privateRow 7 16, 52543055835270⟩, ⟨.privateRow 7 17, 127645581389040⟩, ⟨.privateRow 7 18, 232376210506440⟩, ⟨.privateRow 7 19, 409319018572464⟩, ⟨.privateRow 7 20, 517391183689380⟩, ⟨.privateRow 7 21, 537489620347680⟩, ⟨.privateRow 8 13, 2102605681176⟩, ⟨.privateRow 8 14, 25835939088960⟩, ⟨.privateRow 8 15, 57048639437790⟩, ⟨.privateRow 8 16, 95058979535520⟩, ⟨.privateRow 8 17, 164704111692120⟩, ⟨.privateRow 8 18, 194676549539472⟩, ⟨.privateRow 8 19, 255713955637140⟩, ⟨.privateRow 9 11, 2398694538240⟩, ⟨.privateRow 9 12, 11626172590032⟩, ⟨.privateRow 9 13, 26202406310080⟩, ⟨.privateRow 9 14, 43082802682920⟩, ⟨.privateRow 9 15, 71618165498880⟩, ⟨.privateRow 9 16, 94685968256880⟩, ⟨.privateRow 9 17, 9729704720736⟩, ⟨.privateRow 10 9, 1686582097200⟩, ⟨.privateRow 10 10, 5703714001440⟩, ⟨.privateRow 10 11, 12413244235392⟩, ⟨.privateRow 10 12, 18365005058400⟩, ⟨.privateRow 10 13, 40983944961960⟩, ⟨.privateRow 11 7, 1037896675200⟩, ⟨.privateRow 11 8, 3092067178200⟩, ⟨.privateRow 11 9, 6501007356480⟩, ⟨.privateRow 11 10, 11198905125408⟩, ⟨.privateRow 11 11, 224877612960⟩, ⟨.privateRow 12 5, 588965176800⟩, ⟨.privateRow 12 6, 1902810571200⟩, ⟨.privateRow 12 7, 3023354574240⟩, ⟨.privateRow 13 3, 329820499008⟩, ⟨.privateRow 13 4, 883447765200⟩, ⟨.privateRow 14 1, 143560261845⟩, ⟨.hall 6 23, 610992474412320⟩, ⟨.hall 5 24, 2916685127852496⟩, ⟨.hall 4 25, 7984954280983680⟩, ⟨.hall 3 26, 17250711499781760⟩, ⟨.hall 2 27, 14291711187193440⟩, ⟨.assumptionRow 15, 708548480640⟩]
  caps := #[0, 17693306336946240, 0, 54217992484656, 208234884858000, 19625925959640, 37444442723688, 6867318164850, 64437184812, 0, 1935455627952, 4860018089136, 2337753278784, 708548480640, 10237263141105, 6177931119360, 491891400000, 0, 0, 0, 0] }

theorem case_50_30_15_checked :
    (Witness.linear .conditional case_50_30_15).check 50 30 15 = true := by
  change case_50_30_15.check 50 30 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_30_16 : Certificate := {
  objectiveScale := 122972850000
  eta := 794595712973222160
  rows := #[⟨.count 2, 155803080975141600⟩, ⟨.count 3, 33620664842004240⟩, ⟨.count 4, 6946019709108480⟩, ⟨.count 5, 1587776496005700⟩, ⟨.count 6, 353732485186080⟩, ⟨.count 7, 80393746633200⟩, ⟨.count 8, 19789229940480⟩, ⟨.count 9, 5565720920760⟩, ⟨.count 10, 1686582097200⟩, ⟨.path 10, 187444569312⟩, ⟨.privateRow 2 28, 5740113509610480⟩, ⟨.privateRow 3 25, 60741941900640⟩, ⟨.privateRow 3 26, 3416734231911000⟩, ⟨.privateRow 4 23, 397949045834340⟩, ⟨.privateRow 4 24, 1280940363022320⟩, ⟨.privateRow 5 21, 237965490034272⟩, ⟨.privateRow 5 22, 473318183302965⟩, ⟨.privateRow 5 23, 956685584935080⟩, ⟨.privateRow 6 18, 16078749326640⟩, ⟨.privateRow 6 19, 89103069185130⟩, ⟨.privateRow 6 20, 186245513033580⟩, ⟨.privateRow 6 21, 350717719687335⟩, ⟨.privateRow 6 22, 503800812234720⟩, ⟨.privateRow 7 16, 11197700423910⟩, ⟨.privateRow 7 17, 34454462842800⟩, ⟨.privateRow 7 18, 70344528304050⟩, ⟨.privateRow 7 19, 136324824648012⟩, ⟨.privateRow 7 20, 192370750872300⟩, ⟨.privateRow 7 21, 227016627397560⟩, ⟨.privateRow 7 22, 34454462842800⟩, ⟨.privateRow 8 14, 5428295712840⟩, ⟨.privateRow 8 15, 14378112378630⟩, ⟨.privateRow 8 16, 27828604603800⟩, ⟨.privateRow 8 17, 54214244524440⟩, ⟨.privateRow 8 18, 79342443792612⟩, ⟨.privateRow 8 19, 93689635499460⟩, ⟨.privateRow 8 20, 84001158341100⟩, ⟨.privateRow 9 11, 37479602160⟩, ⟨.privateRow 9 12, 2246902149492⟩, ⟨.privateRow 9 13, 6275751161680⟩, ⟨.privateRow 9 14, 11981760315525⟩, ⟨.privateRow 9 15, 23057986671720⟩, ⟨.privateRow 9 16, 34871646509700⟩, ⟨.privateRow 9 17, 43206485370048⟩, ⟨.privateRow 9 18, 4380428502450⟩, ⟨.privateRow 10 9, 14054850810⟩, ⟨.privateRow 10 10, 889288742160⟩, ⟨.privateRow 10 11, 2782860460380⟩, ⟨.privateRow 10 12, 5621940324000⟩, ⟨.privateRow 10 13, 10878454526940⟩, ⟨.privateRow 10 14, 16865820972000⟩, ⟨.privateRow 10 15, 6015476146680⟩, ⟨.privateRow 11 8, 351371270250⟩, ⟨.privateRow 11 9, 1272602855160⟩, ⟨.privateRow 11 10, 1484192245536⟩, ⟨.privateRow 11 11, 8339211480600⟩, ⟨.privateRow 11 12, 2361214936080⟩, ⟨.privateRow 12 6, 126854038080⟩, ⟨.privateRow 12 7, 601235284650⟩, ⟨.privateRow 12 8, 1480444285320⟩, ⟨.privateRow 12 9, 1875854088108⟩, ⟨.privateRow 13 4, 44172388260⟩, ⟨.privateRow 13 5, 285421585680⟩, ⟨.privateRow 13 6, 747249568065⟩, ⟨.privateRow 14 3, 123051653010⟩, ⟨.privateRow 14 4, 88344776520⟩, ⟨.hall 7 22, 699076057680⟩, ⟨.hall 6 23, 323584830198630⟩, ⟨.hall 5 24, 1233240073353288⟩, ⟨.hall 4 25, 2995594682240160⟩, ⟨.hall 3 26, 6074194190064000⟩, ⟨.hall 2 27, 5037242467617360⟩, ⟨.assumptionRow 16, 134483108760⟩]
  caps := #[0, 0, 669332152288800, 356609490837600, 9531877603248, 24860220112728, 1341486226080, 0, 1214569962606, 1671872193992, 16247729862, 707168655522, 305453011710, 134483108760, 2673090956250, 9184792977360, 1464163941240, 122972850000, 0, 0, 0] }

theorem case_50_30_16_checked :
    (Witness.linear .conditional case_50_30_16).check 50 30 16 = true := by
  change case_50_30_16.check 50 30 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_30_17 : Certificate := {
  objectiveScale := 42332479358400000
  eta := 258623922036957522645600
  rows := #[⟨.count 2, 50258899829044376870400⟩, ⟨.count 3, 10261192048429893611040⟩, ⟨.count 4, 2003786202334449012480⟩, ⟨.count 5, 420877224875575868400⟩, ⟨.count 6, 88281564242193962640⟩, ⟨.count 7, 18477536701854550320⟩, ⟨.count 8, 4421974595315618880⟩, ⟨.count 9, 1421348977065734640⟩, ⟨.count 10, 430711811232040800⟩, ⟨.path 9, 128330111667098880⟩, ⟨.privateRow 2 28, 2931769156694255317440⟩, ⟨.privateRow 3 25, 131852052020641112160⟩, ⟨.privateRow 3 26, 1256472495726109421760⟩, ⟨.privateRow 4 23, 150899883065145494280⟩, ⟨.privateRow 4 24, 458516651490464767200⟩, ⟨.privateRow 5 21, 75757900477603656312⟩, ⟨.privateRow 5 22, 163731505774766709780⟩, ⟨.privateRow 5 23, 354152786785545547800⟩, ⟨.privateRow 6 18, 3372883683671862360⟩, ⟨.privateRow 6 19, 26404628064687212340⟩, ⟨.privateRow 6 20, 61044306437237995872⟩, ⟨.privateRow 6 21, 127546329733634882070⟩, ⟨.privateRow 6 22, 202454491640690289000⟩, ⟨.privateRow 7 16, 2034728743954221315⟩, ⟨.privateRow 7 17, 9364465879511319720⟩, ⟨.privateRow 7 18, 22094832246662054880⟩, ⟨.privateRow 7 19, 48158913118166939088⟩, ⟨.privateRow 7 20, 77099721595238331990⟩, ⟨.privateRow 7 21, 103630629121512292800⟩, ⟨.privateRow 8 14, 815959597945143960⟩, ⟨.privateRow 8 15, 3474408610605129120⟩, ⟨.privateRow 8 16, 8246080176468666840⟩, ⟨.privateRow 8 17, 18582821811266826960⟩, ⟨.privateRow 8 18, 31253884729034320584⟩, ⟨.privateRow 8 19, 42837878892120057900⟩, ⟨.privateRow 8 20, 47062443907287658080⟩, ⟨.privateRow 9 12, 252684262589463936⟩, ⟨.privateRow 9 13, 1304365522163205040⟩, ⟨.privateRow 9 14, 3250677753104041260⟩, ⟨.privateRow 9 15, 7542926052893819280⟩, ⟨.privateRow 9 16, 13344887618006064120⟩, ⟨.privateRow 9 17, 19256646511505397456⟩, ⟨.privateRow 9 18, 22399407027461855160⟩, ⟨.privateRow 9 19, 2597032698836157120⟩, ⟨.privateRow 10 10, 54817866884077920⟩, ⟨.privateRow 10 11, 473782992355244880⟩, ⟨.privateRow 10 12, 1335206614819326480⟩, ⟨.privateRow 10 13, 3278793663003910590⟩, ⟨.privateRow 10 14, 4762442027051422560⟩, ⟨.privateRow 10 15, 12146073076743550560⟩, ⟨.privateRow 10 16, 4281275403646485552⟩, ⟨.privateRow 11 9, 156622476811651200⟩, ⟨.privateRow 11 10, 555618236489332632⟩, ⟨.privateRow 11 11, 1521848399686544160⟩, ⟨.privateRow 11 12, 3074205552668691210⟩, ⟨.privateRow 11 13, 4110221284328617920⟩, ⟨.privateRow 12 7, 30708156911914020⟩, ⟨.privateRow 12 8, 224927279198954640⟩, ⟨.privateRow 12 9, 736995765885936480⟩, ⟨.privateRow 12 10, 1684561750596426240⟩, ⟨.privateRow 12 11, 552746824414452360⟩, ⟨.privateRow 13 6, 65803193382672900⟩, ⟨.privateRow 13 7, 351747979172833320⟩, ⟨.privateRow 13 8, 600125123649976848⟩, ⟨.privateRow 14 4, 11280547437029640⟩, ⟨.privateRow 14 5, 134426523624603210⟩, ⟨.privateRow 14 6, 146647116681385320⟩, ⟨.privateRow 15 3, 52642554706138320⟩, ⟨.privateRow 15 4, 28514717132491590⟩, ⟨.hall 7 22, 43828360002949682160⟩, ⟨.hall 6 23, 214630275856264197930⟩, ⟨.hall 5 24, 573214249684198938816⟩, ⟨.hall 4 25, 1241943150627215245440⟩, ⟨.hall 3 26, 2357824930251464593920⟩, ⟨.hall 2 27, 1974456778998171948480⟩, ⟨.assumptionRow 17, 34042215438831600⟩]
  caps := #[0, 1960957472348761785360, 247839807897131788800, 0, 8663803804171574520, 804198516437488788, 0, 1793277860265741168, 45168569126400720, 0, 0, 1290520163069584020, 93836382396926400, 571091227033185936, 1099760968369442610, 34042215438831600, 2817052109891989200, 473947536861968400, 42332479358400000, 0, 0] }

theorem case_50_30_17_checked :
    (Witness.linear .conditional case_50_30_17).check 50 30 17 = true := by
  change case_50_30_17.check 50 30 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_30_18 : Certificate := {
  objectiveScale := 9869909589540000
  eta := 73324144929159385541280
  rows := #[⟨.count 2, 13940861500199214060480⟩, ⟨.count 3, 2782189097679242291040⟩, ⟨.count 4, 523236912319182821760⟩, ⟨.count 5, 104119452843783577200⟩, ⟨.count 6, 19357419401942862240⟩, ⟨.count 7, 3372883683671862360⟩, ⟨.count 8, 541466276977422720⟩, ⟨.count 9, 67683284622177840⟩, ⟨.path 9, 38456888964278400⟩, ⟨.privateRow 2 28, 747900295075065132000⟩, ⟨.privateRow 3 25, 26592010491557871360⟩, ⟨.privateRow 3 26, 340710134423085226800⟩, ⟨.privateRow 4 23, 37395014753753256600⟩, ⟨.privateRow 4 24, 121814871590004072480⟩, ⟨.privateRow 5 21, 18858819205226152152⟩, ⟨.privateRow 5 22, 42381016720920357480⟩, ⟨.privateRow 5 23, 96298273287443026800⟩, ⟨.privateRow 6 18, 907815484218099600⟩, ⟨.privateRow 6 19, 6371002513602406680⟩, ⟨.privateRow 6 20, 15378394302654607224⟩, ⟨.privateRow 6 21, 33912145732570355250⟩, ⟨.privateRow 6 22, 57404199118724498040⟩, ⟨.privateRow 7 16, 542070592018692165⟩, ⟨.privateRow 7 17, 2178757162123439040⟩, ⟨.privateRow 7 18, 5352619758870564180⟩, ⟨.privateRow 7 19, 12448245247439879592⟩, ⟨.privateRow 7 20, 21478565196798614190⟩, ⟨.privateRow 7 21, 31368516577751564640⟩, ⟨.privateRow 8 14, 214330401303563160⟩, ⟨.privateRow 8 15, 779767841584673865⟩, ⟨.privateRow 8 16, 1909635530411446200⟩, ⟨.privateRow 8 17, 4626904540421657340⟩, ⟨.privateRow 8 18, 8476203344184071496⟩, ⟨.privateRow 8 19, 12769579698717552480⟩, ⟨.privateRow 8 20, 15770205316967436720⟩, ⟨.privateRow 9 12, 66179211630573888⟩, ⟨.privateRow 9 13, 279924695659624400⟩, ⟨.privateRow 9 14, 715374716631629670⟩, ⟨.privateRow 9 15, 1791995535710994240⟩, ⟨.privateRow 9 16, 3489449340521168640⟩, ⟨.privateRow 9 17, 5575598579875850064⟩, ⟨.privateRow 9 18, 7309794739195206720⟩, ⟨.privateRow 9 19, 5963649411709669680⟩, ⟨.privateRow 10 10, 15662247681165120⟩, ⟨.privateRow 10 11, 95987203645997664⟩, ⟨.privateRow 10 12, 277569833905092960⟩, ⟨.privateRow 10 13, 738363104969212800⟩, ⟨.privateRow 10 14, 1525071413239981200⟩, ⟨.privateRow 10 15, 1624398830932268160⟩, ⟨.privateRow 10 16, 5665706225463759552⟩, ⟨.privateRow 11 8, 2051008624914480⟩, ⟨.privateRow 11 9, 29087031407878080⟩, ⟨.privateRow 11 10, 107062650220535856⟩, ⟨.privateRow 11 11, 322008354111573360⟩, ⟨.privateRow 11 12, 720673155579325410⟩, ⟨.privateRow 11 13, 1325537574159015360⟩, ⟨.privateRow 11 14, 1360844222630757480⟩, ⟨.privateRow 12 7, 5640273718514820⟩, ⟨.privateRow 12 8, 38285494331736960⟩, ⟨.privateRow 12 9, 143638970698177416⟩, ⟨.privateRow 12 10, 223104160421252880⟩, ⟨.privateRow 12 11, 1031230044868459590⟩, ⟨.privateRow 13 6, 9400456197524700⟩, ⟨.privateRow 13 7, 60504754434977160⟩, ⟨.privateRow 13 8, 196281525404315736⟩, ⟨.privateRow 13 9, 248172043614652080⟩, ⟨.privateRow 14 5, 19203789089229030⟩, ⟨.privateRow 14 6, 102843432477854640⟩, ⟨.privateRow 14 7, 48184052623883748⟩, ⟨.privateRow 15 4, 40735310189273700⟩, ⟨.privateRow 15 5, 8887704041296080⟩, ⟨.privateRow 16 3, 12220593056782110⟩, ⟨.hall 7 22, 22041699233371697880⟩, ⟨.hall 6 23, 74900014845017552190⟩, ⟨.hall 5 24, 178381552731237103248⟩, ⟨.hall 4 25, 363143383092858170880⟩, ⟨.hall 3 26, 663322928372749124480⟩, ⟨.hall 2 27, 549172502383690682640⟩, ⟨.assumptionRow 18, 4050008775188640⟩]
  caps := #[0, 17355335897818638720, 45042046258288574880, 7294846172444606160, 469824699555597672, 421913358397027728, 61774694413296480, 51895471073025789, 10742624137808640, 63897228152273296, 48114508260289104, 47727063350370900, 5001030273420720, 58440291443797032, 4050008775188640, 193245436917160320, 219589671204461250, 592944018017836320, 104518996709751360, 9869909589540000, 0] }

theorem case_50_30_18_checked :
    (Witness.linear .conditional case_50_30_18).check 50 30 18 = true := by
  change case_50_30_18.check 50 30 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_30_19 : Certificate := {
  objectiveScale := 37074037000000
  eta := 299765127796172438400
  rows := #[⟨.count 2, 50972207965341062400⟩, ⟨.count 3, 9304450660340035200⟩, ⟨.count 4, 1808537724260467200⟩, ⟨.count 5, 391651535681406000⟩, ⟨.count 6, 85270967262280800⟩, ⟨.count 7, 17847411752570400⟩, ⟨.count 8, 3050839615824000⟩, ⟨.count 9, 457625942373600⟩, ⟨.path 4, 44296954394893200⟩, ⟨.path 10, 55607624392320⟩, ⟨.privateRow 7 16, 1115463234535650⟩, ⟨.privateRow 7 17, 6252664661614800⟩, ⟨.privateRow 8 14, 559320596234400⟩, ⟨.privateRow 8 15, 2545544304453150⟩, ⟨.privateRow 9 12, 203389307721600⟩, ⟨.privateRow 9 13, 915251884747200⟩, ⟨.privateRow 9 15, 1953990134896800⟩, ⟨.privateRow 9 18, 71504053495875000⟩, ⟨.privateRow 10 10, 60512521305600⟩, ⟨.privateRow 10 11, 312017687982000⟩, ⟨.privateRow 10 13, 2834160665836500⟩, ⟨.privateRow 10 14, 2216811383186400⟩, ⟨.privateRow 10 15, 3557001642994800⟩, ⟨.privateRow 10 18, 93189282810624000⟩, ⟨.privateRow 11 8, 3466863199800⟩, ⟨.privateRow 11 11, 1331275468723200⟩, ⟨.privateRow 11 12, 2288129711868000⟩, ⟨.privateRow 11 15, 3561161878834560⟩, ⟨.privateRow 11 17, 51309575357040000⟩, ⟨.privateRow 12 8, 13867452799200⟩, ⟨.privateRow 12 15, 18394020517072200⟩, ⟨.privateRow 13 7, 48536084797200⟩, ⟨.privateRow 13 14, 3222449344214100⟩, ⟨.privateRow 15 10, 165253812523800⟩, ⟨.privateRow 15 11, 132203050019040⟩, ⟨.privateRow 15 12, 330507625047600⟩, ⟨.privateRow 15 13, 661015250095200⟩, ⟨.privateRow 16 10, 198304575028560⟩, ⟨.privateRow 16 12, 330507625047600⟩, ⟨.hall 14 5, 378328325375⟩, ⟨.hall 13 6, 3445013221650⟩, ⟨.hall 11 7, 775000934400⟩, ⟨.hall 12 7, 1682448317550⟩, ⟨.hall 7 15, 4336145663850⟩, ⟨.hall 8 16, 10158152804800⟩, ⟨.hall 6 18, 39836437941300⟩, ⟨.hall 5 20, 213047715840960⟩, ⟨.hall 9 20, 13358319175000800⟩, ⟨.hall 4 22, 1312126325205696⟩]
  caps := #[0, 0, 183832722875401600, 530788120502640, 0, 1771181888075600, 732201507797760, 0, 211449187069120, 61376264549600, 456189974988020, 3044091542800, 21127534428000, 16460768724400, 0, 0, 2345140454857200, 7711399696000000, 2001997998000000, 370740370000000, 37074037000000] }

theorem case_50_30_19_checked :
    (Witness.linear .negative case_50_30_19).check 50 30 19 = true := by
  change case_50_30_19.check 50 30 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_31_1_checked :
    (Witness.rising).check 50 31 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_31_2_checked :
    (Witness.rising).check 50 31 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_31_3_checked :
    (Witness.rising).check 50 31 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_31_4_checked :
    (Witness.rising).check 50 31 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_31_5_checked :
    (Witness.rising).check 50 31 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_31_6_checked :
    (Witness.rising).check 50 31 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_31_7_checked :
    (Witness.rising).check 50 31 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_31_8_checked :
    (Witness.rising).check 50 31 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_31_9_checked :
    (Witness.rising).check 50 31 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_31_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_31_10_checked :
    (Witness.linear .positive case_50_31_10).check 50 31 10 = true := by
  change case_50_31_10.check 50 31 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_31_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_31_11_checked :
    (Witness.linear .positive case_50_31_11).check 50 31 11 = true := by
  change case_50_31_11.check 50 31 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_31_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_31_12_checked :
    (Witness.linear .positive case_50_31_12).check 50 31 12 = true := by
  change case_50_31_12.check 50 31 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_31_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_31_13_checked :
    (Witness.linear .positive case_50_31_13).check 50 31 13 = true := by
  change case_50_31_13.check 50 31 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_31_14 : Certificate := {
  objectiveScale := 1633632000
  eta := 26865293160625920
  rows := #[⟨.count 2, 5102323119653760⟩, ⟨.count 3, 955537102840320⟩, ⟨.count 4, 190648027730160⟩, ⟨.count 5, 37261863518880⟩, ⟨.count 6, 7328409557040⟩, ⟨.count 7, 1531309459680⟩, ⟨.count 8, 314114760960⟩, ⟨.count 9, 64250746560⟩, ⟨.path 10, 5289564280⟩, ⟨.hall 10 7, 20076056⟩, ⟨.hall 9 10, 4799088⟩, ⟨.hall 11 10, 12937155⟩, ⟨.hall 10 14, 986700⟩]
  caps := #[0, 23916448035480, 6005362603240, 1421547767640, 350197607760, 116404448160, 0, 0, 0, 15183248080, 13457724280, 29841789120, 1633632000, 1633632000, 0, 0, 0, 0, 0, 0] }

theorem case_50_31_14_checked :
    (Witness.linear .positive case_50_31_14).check 50 31 14 = true := by
  change case_50_31_14.check 50 31 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_31_15 : Certificate := {
  objectiveScale := 34832596500
  eta := 549940892993692200
  rows := #[⟨.count 2, 109988178598738440⟩, ⟨.count 3, 20816177023802160⟩, ⟨.count 4, 4196053701870030⟩, ⟨.count 5, 804829667211570⟩, ⟨.count 6, 167440291375500⟩, ⟨.count 7, 34260859619910⟩, ⟨.count 8, 7212812551560⟩, ⟨.count 9, 1967130695880⟩, ⟨.path 9, 204243238584⟩, ⟨.path 10, 871112627⟩]
  caps := #[0, 0, 0, 15124539834327, 7362015667314, 0, 0, 0, 0, 0, 488527463627, 174162982500, 69665193000, 34832596500, 34832596500, 0, 0, 0, 0, 0] }

theorem case_50_31_15_checked :
    (Witness.linear .positive case_50_31_15).check 50 31 15 = true := by
  change case_50_31_15.check 50 31 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_31_16 : Certificate := {
  objectiveScale := 112648617081000000
  eta := 1249949274299925392793600
  rows := #[⟨.count 2, 236535539754673381622400⟩, ⟨.count 3, 44805167001559825660800⟩, ⟨.count 4, 8424903196874497132800⟩, ⟨.count 5, 1691363141796774045600⟩, ⟨.count 6, 341919772600426020000⟩, ⟨.count 7, 66279832842544120800⟩, ⟨.count 8, 14728851742787582400⟩, ⟨.count 9, 4016959566214795200⟩, ⟨.path 9, 544766017395600000⟩, ⟨.privateRow 2 29, 21700508234373704736000⟩, ⟨.privateRow 3 26, 3148701194791478726400⟩, ⟨.privateRow 3 27, 7020752664062080944000⟩, ⟨.privateRow 4 23, 320720746699199606760⟩, ⟨.privateRow 4 24, 1567702157372953301700⟩, ⟨.privateRow 4 25, 2664694761132653449200⟩, ⟨.privateRow 4 26, 4487697015380591512500⟩, ⟨.privateRow 5 21, 267001351315088229840⟩, ⟨.privateRow 5 22, 580807720390590332640⟩, ⟨.privateRow 5 23, 987692249785097296440⟩, ⟨.privateRow 5 24, 1704128146640523283680⟩, ⟨.privateRow 5 25, 1988149504413943830960⟩, ⟨.privateRow 6 18, 19660386924524496150⟩, ⟨.privateRow 6 19, 115927084805477774400⟩, ⟨.privateRow 6 20, 226806782491615926600⟩, ⟨.privateRow 6 21, 366993889257790594800⟩, ⟨.privateRow 6 22, 630272114160118630200⟩, ⟨.privateRow 6 23, 784136011830310339200⟩, ⟨.privateRow 6 24, 726009650488237915800⟩, ⟨.privateRow 7 16, 15196434337796712000⟩, ⟨.privateRow 7 17, 46685199720442783500⟩, ⟨.privateRow 7 18, 91529292973037119200⟩, ⟨.privateRow 7 19, 144833708804077893600⟩, ⟨.privateRow 7 20, 243446878091503326240⟩, ⟨.privateRow 7 21, 186477783672078498600⟩, ⟨.privateRow 7 22, 548825070891965868000⟩, ⟨.privateRow 7 23, 40504342292665851600⟩, ⟨.privateRow 8 13, 167373315258949800⟩, ⟨.privateRow 8 14, 7794017380558429020⟩, ⟨.privateRow 8 15, 20115792889455263000⟩, ⟨.privateRow 8 16, 38433097516336347825⟩, ⟨.privateRow 8 17, 61370215594948260000⟩, ⟨.privateRow 8 18, 76610485801027077900⟩, ⟨.privateRow 8 19, 182760502041755918280⟩, ⟨.privateRow 8 20, 68888067005329421850⟩, ⟨.privateRow 9 11, 185970350287722000⟩, ⟨.privateRow 9 12, 3530055376370577600⟩, ⟨.privateRow 9 13, 9372905654501188800⟩, ⟨.privateRow 9 14, 17654785253981075200⟩, ⟨.privateRow 9 15, 22706979770130856200⟩, ⟨.privateRow 9 16, 58851645708194539200⟩, ⟨.privateRow 9 17, 43591450107442036800⟩, ⟨.privateRow 10 9, 61799377941766080⟩, ⟨.privateRow 10 10, 1606783826485918080⟩, ⟨.privateRow 10 11, 4637762408266172640⟩, ⟨.privateRow 10 12, 9078328619645437152⟩, ⟨.privateRow 10 13, 14684218858718529120⟩, ⟨.privateRow 10 14, 20687341766006195280⟩, ⟨.privateRow 11 8, 755325730399363200⟩, ⟨.privateRow 11 9, 2454808623797930400⟩, ⟨.privateRow 11 10, 5234220040825339200⟩, ⟨.privateRow 11 11, 7096628566979471520⟩, ⟨.privateRow 12 6, 350686946256847200⟩, ⟨.privateRow 12 7, 1416235744498806000⟩, ⟨.privateRow 12 8, 2659376009114424600⟩, ⟨.privateRow 13 4, 140274778502738880⟩, ⟨.privateRow 13 5, 826619230462568400⟩, ⟨.privateRow 13 6, 80927756828503200⟩, ⟨.privateRow 14 2, 142466571916844175⟩, ⟨.privateRow 14 3, 151964343377967120⟩, ⟨.hall 5 25, 514282406685666418800⟩, ⟨.hall 4 26, 1744550661979062537600⟩, ⟨.hall 3 27, 4239805180245282648000⟩, ⟨.hall 2 28, 8680203293749481894400⟩, ⟨.assumptionRow 16, 128367926961674400⟩]
  caps := #[0, 0, 0, 559380556976459618400, 28356228055303107960, 13843049300324244000, 18579370247695149750, 1312114008641436000, 4786720726542079325, 0, 4199560850722175568, 2741802158853424800, 272455163804023200, 16127931495495108960, 0, 9789937271998884000, 1448712712172325600, 112648617081000000, 0, 0] }

theorem case_50_31_16_checked :
    (Witness.linear .conditional case_50_31_16).check 50 31 16 = true := by
  change case_50_31_16.check 50 31 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_31_17 : Certificate := {
  objectiveScale := 17460372932885883000000
  eta := 178329169258755343355144217600
  rows := #[⟨.count 2, 34124717574206269407465868800⟩, ⟨.count 3, 6361961103730106203574044800⟩, ⟨.count 4, 1226255861596833447635455200⟩, ⟨.count 5, 226634746697764597582790400⟩, ⟨.count 6, 45095689393942955641473600⟩, ⟨.count 7, 9339343957325464186104000⟩, ⟨.count 8, 1867868791465092837220800⟩, ⟨.count 9, 509418761308661682878400⟩, ⟨.path 8, 70012167840888114441600⟩, ⟨.path 9, 46646591737344630071040⟩, ⟨.privateRow 2 29, 3577591358586141147556905600⟩, ⟨.privateRow 3 26, 410100970215002605149811200⟩, ⟨.privateRow 3 27, 1100797341103428045402124800⟩, ⟨.privateRow 4 23, 20639950145689275851289840⟩, ⟨.privateRow 4 24, 219299470297948555919954550⟩, ⟨.privateRow 4 25, 411787240651741925072302200⟩, ⟨.privateRow 4 26, 754268766353497801330224300⟩, ⟨.privateRow 5 21, 23203081209533042133476160⟩, ⟨.privateRow 5 22, 79322161344217609153976640⟩, ⟨.privateRow 5 23, 151764339306538793024190000⟩, ⟨.privateRow 5 24, 288149892230014988355262080⟩, ⟨.privateRow 5 25, 372733217336859275667410640⟩, ⟨.privateRow 6 19, 12265036401099869803587600⟩, ⟨.privateRow 6 20, 29244747288593348370058200⟩, ⟨.privateRow 6 21, 55560201932793820989046320⟩, ⟨.privateRow 6 22, 106885456111605178515608100⟩, ⟨.privateRow 6 23, 150704397889159791930052800⟩, ⟨.privateRow 6 24, 161448349528956030293352600⟩, ⟨.privateRow 7 16, 326135820732000336657600⟩, ⟨.privateRow 7 17, 4753058978281709451856500⟩, ⟨.privateRow 7 18, 11550290690080063870977600⟩, ⟨.privateRow 7 19, 21191416169836112784183600⟩, ⟨.privateRow 7 20, 41093113412232042418857600⟩, ⟨.privateRow 7 21, 59705091727187788904022000⟩, ⟨.privateRow 7 22, 70489810344575527309404000⟩, ⟨.privateRow 7 23, 54835290949439511149839200⟩, ⟨.privateRow 8 14, 202352452408718390698920⟩, ⟨.privateRow 8 15, 1781393384452820020682800⟩, ⟨.privateRow 8 16, 4621029562218328633749375⟩, ⟨.privateRow 8 17, 8716721026837099907030400⟩, ⟨.privateRow 8 18, 16797847812133994612506500⟩, ⟨.privateRow 8 19, 25262925404565380623411320⟩, ⟨.privateRow 8 20, 31033861691529407035074750⟩, ⟨.privateRow 8 21, 20857868171360203348965600⟩, ⟨.privateRow 9 12, 72039016750719833942400⟩, ⟨.privateRow 9 13, 684885223537200706980960⟩, ⟨.privateRow 9 14, 1911892635034977180185600⟩, ⟨.privateRow 9 15, 3799414928093768384801400⟩, ⟨.privateRow 9 16, 7536163262534487118137600⟩, ⟨.privateRow 9 17, 11669463106274342624455200⟩, ⟨.privateRow 9 18, 14795784911787129322712640⟩, ⟨.privateRow 10 10, 16980625376955389429280⟩, ⟨.privateRow 10 11, 268602619599112523699520⟩, ⟨.privateRow 10 12, 830352580933118543091792⟩, ⟨.privateRow 10 13, 1771645247662345630454880⟩, ⟨.privateRow 10 14, 1763862461031241076966460⟩, ⟨.privateRow 10 15, 9926388434643064792087680⟩, ⟨.privateRow 10 16, 305651256785197009727040⟩, ⟨.privateRow 11 9, 94336807649752163496000⟩, ⟨.privateRow 11 10, 380777659968090550838400⟩, ⟨.privateRow 11 11, 894312936519650509942080⟩, ⟨.privateRow 11 12, 1993651201664762388548800⟩, ⟨.privateRow 11 13, 1818341967448972951385400⟩, ⟨.privateRow 12 7, 29933794735017513417000⟩, ⟨.privateRow 12 8, 175112699199852453489450⟩, ⟨.privateRow 12 9, 488192979587467446091800⟩, ⟨.privateRow 12 10, 996196688781382846517760⟩, ⟨.privateRow 13 5, 9529942813597412434800⟩, ⟨.privateRow 13 6, 71841107364042032200800⟩, ⟨.privateRow 13 7, 277956665396591196015000⟩, ⟨.privateRow 13 8, 157677235643157187557600⟩, ⟨.privateRow 14 4, 20648209429461060275400⟩, ⟨.privateRow 14 5, 111182666158636478406000⟩, ⟨.hall 6 24, 25114830093242076834174528⟩, ⟨.hall 5 25, 132929995659265773582213600⟩, ⟨.hall 4 26, 357939004705199642214089600⟩, ⟨.hall 3 27, 773564518065329162157585600⟩, ⟨.hall 2 28, 1461403366637309646482131200⟩, ⟨.assumptionRow 17, 15311477216836709508600⟩]
  caps := #[0, 1977152757449168236059322200, 96281657552478663120055200, 36575243693452184336616000, 5783658819314769996512910, 1730053034802153434973600, 2565512271135220708832388, 323023046256513960502860, 283661280189599970938280, 689355822555801537594640, 212578961089377047124960, 788656954861119783166000, 57343440512247830787000, 15311477216836709508600, 15311477216836709508600, 6090170459918770731105600, 1357072882924015536879600, 211673370910679769491400, 17460372932885883000000, 0] }

theorem case_50_31_17_checked :
    (Witness.linear .conditional case_50_31_17).check 50 31 17 = true := by
  change case_50_31_17.check 50 31 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_31_18 : Certificate := {
  objectiveScale := 3368073352644000000
  eta := 42919576762950131397753600
  rows := #[⟨.count 2, 7679693389041581952844800⟩, ⟨.count 3, 1322451945076894804972800⟩, ⟨.count 4, 225417945183561614484000⟩, ⟨.count 5, 37341962636468792702400⟩, ⟨.count 6, 5855011563209392584000⟩, ⟨.count 7, 840719609076220473600⟩, ⟨.count 8, 140119934846036745600⟩, ⟨.count 9, 57321791527924123200⟩, ⟨.path 8, 46380047070796639200⟩, ⟨.privateRow 2 29, 789645892824840079828800⟩, ⟨.privateRow 3 26, 94113889571588014128000⟩, ⟨.privateRow 3 27, 243178146925296771988800⟩, ⟨.privateRow 4 23, 6284379077844748040160⟩, ⟨.privateRow 4 24, 46108216060273966599000⟩, ⟨.privateRow 4 25, 89142551049863002091400⟩, ⟨.privateRow 4 26, 168721916546483996295600⟩, ⟨.privateRow 5 21, 5434318139778791783520⟩, ⟨.privateRow 5 22, 16084367320976558027424⟩, ⟨.privateRow 5 23, 31877285177473359624000⟩, ⟨.privateRow 5 24, 63754570354946719248000⟩, ⟨.privateRow 5 25, 87434839343926929254400⟩, ⟨.privateRow 6 18, 191101071854751007950⟩, ⟨.privateRow 6 19, 2369885632727611284000⟩, ⟨.privateRow 6 20, 5757428037155902707600⟩, ⟨.privateRow 6 21, 11319689022204825662400⟩, ⟨.privateRow 6 22, 23176087437703845645000⟩, ⟨.privateRow 6 23, 35303551203351448617600⟩, ⟨.privateRow 6 24, 41147720152554897882000⟩, ⟨.privateRow 7 16, 141788029308489564000⟩, ⟨.privateRow 7 17, 855732459238295839200⟩, ⟨.privateRow 7 18, 2142548187416184319200⟩, ⟨.privateRow 7 19, 4186083053525347774800⟩, ⟨.privateRow 7 20, 8701447953938881901760⟩, ⟨.privateRow 7 21, 13811822149109336352000⟩, ⟨.privateRow 7 22, 18085480161913457092800⟩, ⟨.privateRow 7 23, 16461590202715638380400⟩, ⟨.privateRow 8 14, 59550972309565616880⟩, ⟨.privateRow 8 15, 308458467681900335800⟩, ⟨.privateRow 8 16, 811163060319634597575⟩, ⟨.privateRow 8 17, 1641404951053573305600⟩, ⟨.privateRow 8 18, 3457751308856885940900⟩, ⟨.privateRow 8 19, 5720396340089450139120⟩, ⟨.privateRow 8 20, 7853284473323965726050⟩, ⟨.privateRow 8 21, 8421791917308666897000⟩, ⟨.privateRow 8 22, 2473992599625336289500⟩, ⟨.privateRow 9 12, 18528255847409817600⟩, ⟨.privateRow 9 13, 113369765466338821440⟩, ⟨.privateRow 9 14, 318454397377356240000⟩, ⟨.privateRow 9 15, 678307866413768791200⟩, ⟨.privateRow 9 16, 1482177752364895185600⟩, ⟨.privateRow 9 17, 2558250325598095128000⟩, ⟨.privateRow 9 18, 3711904455830464333440⟩, ⟨.privateRow 9 19, 3171805797878468150400⟩, ⟨.privateRow 10 10, 3821452768528274880⟩, ⟨.privateRow 10 11, 40646361265255287360⟩, ⟨.privateRow 10 12, 131840120514225483360⟩, ⟨.privateRow 10 13, 299347133534714865600⟩, ⟨.privateRow 10 14, 687144975940990426860⟩, ⟨.privateRow 10 15, 1259441648142104306880⟩, ⟨.privateRow 10 16, 1941298006412363639040⟩, ⟨.privateRow 10 17, 325587775878609019776⟩, ⟨.privateRow 11 9, 13268933224056510000⟩, ⟨.privateRow 11 10, 56163775537461009600⟩, ⟨.privateRow 11 11, 142030661230300883040⟩, ⟨.privateRow 11 12, 348884484237859169600⟩, ⟨.privateRow 11 13, 687065362341646087800⟩, ⟨.privateRow 11 14, 539552736127920715200⟩, ⟨.privateRow 12 7, 2694614131654552800⟩, ⟨.privateRow 12 8, 23353322474339457600⟩, ⟨.privateRow 12 9, 71652239409905154000⟩, ⟨.privateRow 12 10, 195292159191663714180⟩, ⟨.privateRow 12 11, 349326782011994386600⟩, ⟨.privateRow 13 6, 6929007767111707200⟩, ⟨.privateRow 13 7, 36281054558348800200⟩, ⟨.privateRow 13 8, 118737996736414255200⟩, ⟨.privateRow 13 9, 58550115632093925840⟩, ⟨.privateRow 14 4, 2323417286987854200⟩, ⟨.privateRow 14 5, 15012850162075365600⟩, ⟨.privateRow 14 6, 54213070029716598000⟩, ⟨.privateRow 15 3, 6505568403565991760⟩, ⟨.privateRow 15 4, 14011993484603674560⟩, ⟨.hall 6 24, 10140880027478667955488⟩, ⟨.hall 5 25, 36763967905228891126800⟩, ⟨.hall 4 26, 88851607574036856348800⟩, ⟨.hall 3 27, 181505358459491170104000⟩, ⟨.hall 2 28, 333156887844962954572800⟩, ⟨.assumptionRow 18, 1804192693177574700⟩]
  caps := #[0, 15680683665129010928400, 1566365755207243290300, 2439461926224875872320, 1734097628766135512880, 133007534456051335080, 176645581217170043550, 43600470089295791100, 10259587990936028745, 0, 18535511428964970804, 13550066242566357840, 1804192693177574700, 223360992999679938480, 2044504726888724100, 1804192693177574700, 1016448331039418277000, 235887143142279528900, 38612687538550425300, 3368073352644000000] }

theorem case_50_31_18_checked :
    (Witness.linear .conditional case_50_31_18).check 50 31 18 = true := by
  change case_50_31_18.check 50 31 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_31_19 : Certificate := {
  objectiveScale := 722498190326312400000
  eta := 11700716565349368792938102400
  rows := #[⟨.count 2, 2258532475712205817290566400⟩, ⟨.count 3, 411961682421059785753939200⟩, ⟨.count 4, 78289466069855873918685600⟩, ⟨.count 5, 13676234714520277440340800⟩, ⟨.count 6, 2452152871553927296154400⟩, ⟨.count 7, 386455612027260587011200⟩, ⟨.count 8, 42939512447473398556800⟩, ⟨.path 8, 1680481378195759339200⟩, ⟨.path 9, 4562507788004700293760⟩, ⟨.privateRow 4 23, 544258320271725326707440⟩, ⟨.privateRow 4 24, 12062648348330066135198550⟩, ⟨.privateRow 5 22, 6793460264314766385671328⟩, ⟨.privateRow 5 23, 8575557379666031109274920⟩, ⟨.privateRow 6 19, 464228708552021079295200⟩, ⟨.privateRow 6 20, 1623139129748094151993800⟩, ⟨.privateRow 6 21, 3845693405876037198603120⟩, ⟨.privateRow 6 22, 6720992169289575119642700⟩, ⟨.privateRow 7 16, 26070418271680277695200⟩, ⟨.privateRow 7 17, 207029792157461028756000⟩, ⟨.privateRow 7 18, 569824856509583212480800⟩, ⟨.privateRow 7 19, 703901293335367497770400⟩, ⟨.privateRow 7 21, 11723637063672223700610600⟩, ⟨.privateRow 8 14, 17444176931786068163700⟩, ⟨.privateRow 8 15, 79020630545697573733000⟩, ⟨.privateRow 8 16, 214697562237366992784000⟩, ⟨.privateRow 8 17, 456232319754404859666000⟩, ⟨.privateRow 8 18, 336359514171874955361600⟩, ⟨.privateRow 8 20, 7676108779867861763880450⟩, ⟨.privateRow 8 21, 1332914032223653413534000⟩, ⟨.privateRow 9 12, 8162056085056926998400⟩, ⟨.privateRow 9 13, 30448017917299318976640⟩, ⟨.privateRow 9 15, 346443793610296738356000⟩, ⟨.privateRow 9 16, 331805323457748988848000⟩, ⟨.privateRow 9 17, 390033904731216703557600⟩, ⟨.privateRow 9 18, 304089819968925249779520⟩, ⟨.privateRow 9 20, 4301107830155252088772800⟩, ⟨.privateRow 10 10, 3220463433560504891760⟩, ⟨.privateRow 10 11, 12615699731468424121440⟩, ⟨.privateRow 10 12, 26173584632755376120304⟩, ⟨.privateRow 10 13, 20103499009498909324320⟩, ⟨.privateRow 10 17, 2392862885016065325575712⟩, ⟨.privateRow 11 8, 1201105243285969190400⟩, ⟨.privateRow 11 9, 5530088724295816480800⟩, ⟨.privateRow 11 10, 14904624155321344953600⟩, ⟨.privateRow 11 11, 29276940305095499016000⟩, ⟨.privateRow 11 12, 33180532345774898884800⟩, ⟨.privateRow 11 17, 1492636006554785524832400⟩, ⟨.privateRow 12 6, 383388503995298201400⟩, ⟨.privateRow 12 8, 11405807993860121491650⟩, ⟨.privateRow 12 13, 75527535287073745675800⟩, ⟨.privateRow 13 4, 306710803196238561120⟩, ⟨.privateRow 13 6, 2123382483666266961600⟩, ⟨.privateRow 14 12, 63131306991225770497200⟩, ⟨.privateRow 16 7, 116294512878573787758000⟩, ⟨.privateRow 16 14, 889653023521089476348700⟩, ⟨.privateRow 17 13, 5023922956354387631145600⟩, ⟨.hall 13 4, 169392567778314760880⟩, ⟨.hall 14 4, 480814288539985744344⟩, ⟨.hall 12 6, 60535026946626031800⟩, ⟨.hall 11 7, 37735478398918024725⟩, ⟨.hall 8 12, 2361652426321372800⟩, ⟨.hall 6 18, 13917245382037411128⟩, ⟨.hall 7 19, 149415440687495662680⟩, ⟨.hall 5 20, 571395356679158531520⟩, ⟨.hall 6 23, 356459295474668455733664⟩]
  caps := #[0, 0, 841514647256003898777600, 1151302100372857220467680, 107496261842769184194810, 223088169239718701510592, 0, 7304096718369492683928, 24391976075978937956530, 5753342441631261597120, 2399416581936136160160, 0, 17448344198133843144150, 0, 66025680614573951070800, 21617097688017245253840, 674917530128730352163700, 111264721310252109600000, 46962382371210306000000, 7947480093589436400000] }

theorem case_50_31_19_checked :
    (Witness.linear .negative case_50_31_19).check 50 31 19 = true := by
  change case_50_31_19.check 50 31 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_31_20 : Certificate := {
  objectiveScale := 155443813516426985550000
  eta := 2480160830515778792108453126400
  rows := #[⟨.count 2, 454402989042489022194811152000⟩, ⟨.count 3, 76049987919445031798068963200⟩, ⟨.count 4, 12933671414871604047290640000⟩, ⟨.count 5, 1983162950280312620584564800⟩, ⟨.count 6, 277150101747248658156228000⟩, ⟨.count 7, 29846934034319086262978400⟩, ⟨.path 7, 547786805975852550307200⟩, ⟨.path 8, 2420267940282698459553600⟩, ⟨.privateRow 8 14, 829081500953307951749400⟩, ⟨.privateRow 8 15, 3500566337358411351830800⟩, ⟨.privateRow 9 12, 383707140937068142958400⟩, ⟨.privateRow 9 13, 1688311420123099829016960⟩, ⟨.privateRow 10 10, 135667881974177664831720⟩, ⟨.privateRow 10 11, 592005303160047991992960⟩, ⟨.privateRow 11 8, 46382181871513731566400⟩, ⟨.privateRow 11 9, 251236818470699379318000⟩, ⟨.privateRow 11 10, 548153058481525918512000⟩, ⟨.hall 14 5, 5573657149265935810080⟩, ⟨.hall 15 7, 5652828415590736034655⟩, ⟨.hall 13 9, 5256972083966734911780⟩, ⟨.hall 10 10, 5499464804683019108400⟩, ⟨.hall 11 10, 5860596896690879781900⟩, ⟨.hall 12 10, 6015734114914374958800⟩, ⟨.hall 14 10, 4433590914188812576200⟩, ⟨.hall 9 11, 4831819178488131600540⟩, ⟨.hall 9 13, 210921344926549115040⟩, ⟨.hall 8 15, 16809430693345150961100⟩, ⟨.hall 7 16, 17101959765867906329400⟩, ⟨.hall 6 18, 19086723799091331802848⟩]
  caps := #[0, 1407241212754931171713695600, 0, 0, 47393722318272904606032000, 3873061783239725831554800, 5880483376580391297919200, 3071429618259338312776800, 6197194777958879128634200, 98431775199026549897400, 288566001833401693462320, 0, 4202052824707448997686400, 1627807615144023392679600, 4187449077714521088069600, 5925829058873229543137100, 0, 99017709209963989795350000, 32332313211416812994400000, 8393965929887057219700000] }

theorem case_50_31_20_checked :
    (Witness.linear .negative case_50_31_20).check 50 31 20 = true := by
  change case_50_31_20.check 50 31 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_32_1_checked :
    (Witness.rising).check 50 32 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_32_2_checked :
    (Witness.rising).check 50 32 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_32_3_checked :
    (Witness.rising).check 50 32 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_32_4_checked :
    (Witness.rising).check 50 32 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_32_5_checked :
    (Witness.rising).check 50 32 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_32_6_checked :
    (Witness.rising).check 50 32 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_32_7_checked :
    (Witness.rising).check 50 32 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_32_8_checked :
    (Witness.rising).check 50 32 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_32_9_checked :
    (Witness.rising).check 50 32 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_32_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_32_10_checked :
    (Witness.linear .positive case_50_32_10).check 50 32 10 = true := by
  change case_50_32_10.check 50 32 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_32_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_32_11_checked :
    (Witness.linear .positive case_50_32_11).check 50 32 11 = true := by
  change case_50_32_11.check 50 32 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_32_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_32_12_checked :
    (Witness.linear .positive case_50_32_12).check 50 32 12 = true := by
  change case_50_32_12.check 50 32 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_32_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_50_32_13_checked :
    (Witness.linear .positive case_50_32_13).check 50 32 13 = true := by
  change case_50_32_13.check 50 32 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_32_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_50_32_14_checked :
    (Witness.linear .positive case_50_32_14).check 50 32 14 = true := by
  change case_50_32_14.check 50 32 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_32_15 : Certificate := {
  objectiveScale := 877655000
  eta := 62812182160607880
  rows := #[⟨.count 2, 7113246974914080⟩, ⟨.count 3, 943288418467395⟩, ⟨.count 4, 146503402721676⟩, ⟨.count 5, 24351419140620⟩, ⟨.count 6, 4252638685680⟩, ⟨.count 7, 708773114280⟩, ⟨.count 8, 128867838960⟩, ⟨.count 9, 57990527532⟩, ⟨.path 3, 81366877732140⟩, ⟨.path 8, 24528285600⟩]
  caps := #[0, 0, 0, 0, 298386594324, 0, 0, 11136879120, 11510906640, 0, 12287170000, 4388275000, 1755310000, 877655000, 877655000, 0, 0, 0, 0] }

theorem case_50_32_15_checked :
    (Witness.linear .positive case_50_32_15).check 50 32 15 = true := by
  change case_50_32_15.check 50 32 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_32_16 : Certificate := {
  objectiveScale := 144949210560000
  eta := 4078562030536060267200
  rows := #[⟨.count 2, 717623095430082441600⟩, ⟨.count 3, 96337715843609440200⟩, ⟨.count 4, 18046734648389647200⟩, ⟨.count 5, 3033064646788176000⟩, ⟨.count 6, 489956596788859200⟩, ⟨.count 7, 81659432798143200⟩, ⟨.count 8, 14847169599662400⟩, ⟨.path 8, 3516752714675200⟩, ⟨.privateRow 2 30, 55201776571544803200⟩, ⟨.privateRow 3 12, 280137220849185700⟩, ⟨.privateRow 3 27, 10792655034821259600⟩, ⟨.privateRow 3 28, 17515948335201716400⟩, ⟨.privateRow 4 24, 1942677906267826728⟩, ⟨.privateRow 4 25, 4378987083800429100⟩, ⟨.privateRow 4 26, 6652521791955399360⟩, ⟨.privateRow 4 27, 10297254475845857520⟩, ⟨.privateRow 5 21, 275142292958641680⟩, ⟨.privateRow 5 22, 947832702121305000⟩, ⟨.privateRow 5 23, 1619656521384885984⟩, ⟨.privateRow 5 24, 2430243048239026020⟩, ⟨.privateRow 5 25, 3862102316910277440⟩, ⟨.privateRow 5 26, 3988480010526451440⟩, ⟨.privateRow 6 18, 27219810932714400⟩, ⟨.privateRow 6 19, 177171805088828550⟩, ⟨.privateRow 6 20, 384132637958612400⟩, ⟨.privateRow 6 21, 634804876395089400⟩, ⟨.privateRow 6 22, 911085957362140560⟩, ⟨.privateRow 6 23, 1431956482281725400⟩, ⟨.privateRow 6 24, 1570971945259516800⟩, ⟨.privateRow 6 25, 1169479734001979400⟩, ⟨.privateRow 7 16, 25372752333708780⟩, ⟨.privateRow 7 17, 83927750375869400⟩, ⟨.privateRow 7 18, 162954314557008975⟩, ⟨.privateRow 7 19, 261226859002223400⟩, ⟨.privateRow 7 20, 369897787853493900⟩, ⟨.privateRow 7 21, 326637731192572800⟩, ⟨.privateRow 7 22, 1119171690581694750⟩, ⟨.privateRow 8 13, 463974049989450⟩, ⟨.privateRow 8 14, 14847169599662400⟩, ⟨.privateRow 8 15, 39901768299092700⟩, ⟨.privateRow 8 16, 75060690753848800⟩, ⟨.privateRow 8 17, 117849408697320300⟩, ⟨.privateRow 8 18, 165439889824809600⟩, ⟨.privateRow 8 19, 252092567160934500⟩, ⟨.privateRow 8 20, 139934573476818120⟩, ⟨.privateRow 9 11, 342626990761440⟩, ⟨.privateRow 9 12, 7918490453153280⟩, ⟨.privateRow 9 13, 20651063170439520⟩, ⟨.privateRow 9 14, 38305697567128992⟩, ⟨.privateRow 9 15, 60378489705293760⟩, ⟨.privateRow 9 16, 84628866718075680⟩, ⟨.privateRow 9 17, 52813503290227680⟩, ⟨.privateRow 10 9, 212102422852320⟩, ⟨.privateRow 10 10, 4339941882978240⟩, ⟨.privateRow 10 11, 11877735679729920⟩, ⟨.privateRow 10 12, 22540702937669280⟩, ⟨.privateRow 10 13, 35781678735186384⟩, ⟨.privateRow 10 14, 7588553350938560⟩, ⟨.privateRow 11 8, 2518716271371300⟩, ⟨.privateRow 11 9, 7709107292132400⟩, ⟨.privateRow 11 10, 13919221499683500⟩, ⟨.privateRow 12 6, 1555417767583680⟩, ⟨.privateRow 12 7, 4999557110090400⟩, ⟨.privateRow 13 4, 1093653117832275⟩, ⟨.privateRow 13 5, 388854441895920⟩, ⟨.hall 5 26, 345432362550875600⟩, ⟨.hall 4 27, 2562939626536008720⟩, ⟨.hall 3 28, 7659795588591346200⟩, ⟨.hall 2 29, 18117506156814704640⟩, ⟨.assumptionRow 16, 172265548150080⟩]
  caps := #[0, 16524787012601313600, 3304092106597744000, 144776931165731480, 31221673057112384, 0, 0, 1341476732926330, 14851882356456530, 7963413214979376, 1542022410741120, 8654169007333080, 621778535169330, 172265548150080, 72845477601019200, 14492707286238720, 2001972610249920, 144949210560000, 0] }

theorem case_50_32_16_checked :
    (Witness.linear .conditional case_50_32_16).check 50 32 16 = true := by
  change case_50_32_16.check 50 32 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_32_17 : Certificate := {
  objectiveScale := 173176784024731987500
  eta := 5386218750108602566461100800
  rows := #[⟨.count 2, 809217284396284487330006400⟩, ⟨.count 3, 123630418449432352230973200⟩, ⟨.count 4, 18624842259914484232198560⟩, ⟨.count 5, 2675983083321046585086000⟩, ⟨.count 6, 388164579119096867287200⟩, ⟨.count 7, 61753455768947228886600⟩, ⟨.count 8, 14970534731865994881600⟩, ⟨.path 7, 12425176805416272097200⟩, ⟨.path 8, 428634148821931852800⟩, ⟨.privateRow 2 30, 72786739866332467114339200⟩, ⟨.privateRow 3 27, 13201516544383829819757600⟩, ⟨.privateRow 3 28, 22879655362394948302485300⟩, ⟨.privateRow 4 24, 1948115684657721913942608⟩, ⟨.privateRow 4 25, 5244926843309251306768560⟩, ⟨.privateRow 4 26, 8598825641071629693409680⟩, ⟨.privateRow 4 27, 14262989834101178298508380⟩, ⟨.privateRow 5 21, 209709694692914671157760⟩, ⟨.privateRow 5 22, 981193797217717081198200⟩, ⟨.privateRow 5 23, 1896125156181770151718080⟩, ⟨.privateRow 5 24, 3130900207485624504550620⟩, ⟨.privateRow 5 25, 5443714158070243338803520⟩, ⟨.privateRow 5 26, 6277091746875940703873160⟩, ⟨.privateRow 6 18, 5227805779381775990400⟩, ⟨.privateRow 6 19, 145561717169661325232700⟩, ⟨.privateRow 6 20, 389004762190783224142800⟩, ⟨.privateRow 6 21, 728298692640123667662600⟩, ⟨.privateRow 6 22, 1169198762558734200252960⟩, ⟨.privateRow 6 23, 2042275001501611926749700⟩, ⟨.privateRow 6 24, 2564238734786761123291200⟩, ⟨.privateRow 6 25, 2331928115465483452717800⟩, ⟨.privateRow 7 16, 6175345576894722888660⟩, ⟨.privateRow 7 17, 66981261548329004877000⟩, ⟨.privateRow 7 18, 159162180642584226832725⟩, ⟨.privateRow 7 19, 294064075090224899460000⟩, ⟨.privateRow 7 20, 470012413352542797636900⟩, ⟨.privateRow 7 21, 812793103549381622107440⟩, ⟨.privateRow 7 22, 1055690029573907389061400⟩, ⟨.privateRow 7 23, 1060591097492077804052400⟩, ⟨.privateRow 7 24, 245543502700337791049100⟩, ⟨.privateRow 8 14, 3232274544380157985800⟩, ⟨.privateRow 8 15, 28818279358842040147080⟩, ⟨.privateRow 8 16, 69654571321876503963000⟩, ⟨.privateRow 8 17, 128185203641602581173700⟩, ⟨.privateRow 8 18, 205310190608447929804800⟩, ⟨.privateRow 8 19, 242959303252575208599300⟩, ⟨.privateRow 8 20, 702866605661108459691120⟩, ⟨.privateRow 8 21, 166547198892009193057800⟩, ⟨.privateRow 9 12, 1247544560988832906800⟩, ⟨.privateRow 9 13, 12656906636941250218080⟩, ⟨.privateRow 9 14, 32935176410105188739520⟩, ⟨.privateRow 9 15, 62044549499844623231520⟩, ⟨.privateRow 9 16, 81402282604521347168700⟩, ⟨.privateRow 9 17, 212153863628729527464960⟩, ⟨.privateRow 9 18, 157440123596790712838160⟩, ⟨.privateRow 10 10, 345473878427676804960⟩, ⟨.privateRow 10 11, 5738704980548631371280⟩, ⟨.privateRow 10 12, 16875875515921666957440⟩, ⟨.privateRow 10 13, 33683703146698488483600⟩, ⟨.privateRow 10 14, 56056335607098225278880⟩, ⟨.privateRow 10 15, 82150809341114646912780⟩, ⟨.privateRow 11 9, 2735001537552441372600⟩, ⟨.privateRow 11 10, 9356584207416246801000⟩, ⟨.privateRow 11 11, 20754604969177856540400⟩, ⟨.privateRow 11 12, 31625254621066914187380⟩, ⟨.privateRow 12 7, 1260274607529535283400⟩, ⟨.privateRow 12 8, 5655078367119709605000⟩, ⟨.privateRow 12 9, 13232883379060120475700⟩, ⟨.privateRow 13 5, 784170866907266398560⟩, ⟨.privateRow 13 6, 3780823822588605850200⟩, ⟨.privateRow 13 7, 1357218808108730305200⟩, ⟨.privateRow 14 4, 1019422126979446318128⟩, ⟨.hall 5 26, 1127027795938387873930400⟩, ⟨.hall 4 27, 4510942911884049957716400⟩, ⟨.hall 3 28, 11543637369774583717043400⟩, ⟨.hall 2 29, 24975842110996434794136000⟩, ⟨.assumptionRow 17, 162318180997233100224⟩]
  caps := #[0, 3575491768433609838613800, 5695808175359002891949220, 325676993747837120059440, 83493102714587532223488, 0, 39188488201922523750000, 9656243259791192112048, 8877518122559406925332, 6112676133926862954300, 2034126131771538091980, 12846484858766187489840, 13454478151746361618284, 162318180997233100224, 80165590335382109830272, 74892306970783462273344, 15575612823613630196640, 2262156795349014724776, 173176784024731987500] }

theorem case_50_32_17_checked :
    (Witness.linear .conditional case_50_32_17).check 50 32 17 = true := by
  change case_50_32_17.check 50 32 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_32_18 : Certificate := {
  objectiveScale := 256122462815299080000
  eta := 8981968954837627124154979200
  rows := #[⟨.count 2, 1282290346493673138676454400⟩, ⟨.count 3, 181064146148412179303851200⟩, ⟨.count 4, 24537654778582634135166720⟩, ⟨.count 5, 3038937659789899964896800⟩, ⟨.count 6, 358801226379487294603200⟩, ⟨.count 7, 57082013287645705959600⟩, ⟨.count 8, 13838063827308049929600⟩, ⟨.path 6, 32623213852301879664000⟩, ⟨.path 7, 14568775833125035922400⟩, ⟨.privateRow 2 30, 118730587638303068395968000⟩, ⟨.privateRow 3 27, 20283142054876774184311200⟩, ⟨.privateRow 3 28, 36855953246056577481248400⟩, ⟨.privateRow 4 24, 2770380378227071595905920⟩, ⟨.privateRow 4 25, 7903004739674547990106620⟩, ⟨.privateRow 4 26, 13686998297193270384535200⟩, ⟨.privateRow 4 27, 23944001840391118793186880⟩, ⟨.privateRow 5 21, 272595736924675412133600⟩, ⟨.privateRow 5 22, 1338074876558653627954560⟩, ⟨.privateRow 5 23, 2778861134486950386505632⟩, ⟨.privateRow 5 24, 4908237685404850059583320⟩, ⟨.privateRow 5 25, 9140370635647140979689600⟩, ⟨.privateRow 5 26, 11434886357069902658611680⟩, ⟨.privateRow 6 18, 7248509623828026153600⟩, ⟨.privateRow 6 19, 172605135417404872782600⟩, ⟨.privateRow 6 20, 511019928479875843828800⟩, ⟨.privateRow 6 21, 1034724748801450733426400⟩, ⟨.privateRow 6 22, 1798355237671733288708160⟩, ⟨.privateRow 6 23, 3405893459496193788922800⟩, ⟨.privateRow 6 24, 4724216147329916045608800⟩, ⟨.privateRow 6 25, 4870998467212433575219200⟩, ⟨.privateRow 7 16, 5980020439658121576720⟩, ⟨.privateRow 7 17, 74599244878563435830800⟩, ⟨.privateRow 7 18, 198767724840909154680750⟩, ⟨.privateRow 7 19, 402292284122455451524800⟩, ⟨.privateRow 7 20, 703558465362807788533800⟩, ⟨.privateRow 7 21, 1336806387374483723377680⟩, ⟨.privateRow 7 22, 1936711165116550737915000⟩, ⟨.privateRow 7 23, 2243413728574774094539200⟩, ⟨.privateRow 7 24, 1607810040935354051195400⟩, ⟨.privateRow 8 14, 2201510154344462488800⟩, ⟨.privateRow 8 15, 29924813026553657972760⟩, ⟨.privateRow 8 16, 81875210978239295416800⟩, ⟨.privateRow 8 17, 167570304158808417116250⟩, ⟨.privateRow 8 18, 296035722591340068136800⟩, ⟨.privateRow 8 19, 569090374898043553354800⟩, ⟨.privateRow 8 20, 578777019577159188305520⟩, ⟨.privateRow 8 21, 1616026391332818205841100⟩, ⟨.privateRow 9 12, 345951595682701248240⟩, ⟨.privateRow 9 13, 11825254543335969939840⟩, ⟨.privateRow 9 14, 35978965951000929816960⟩, ⟨.privateRow 9 15, 76263107314942141834240⟩, ⟨.privateRow 9 16, 137169807688191044927160⟩, ⟨.privateRow 9 17, 246317536126083288746880⟩, ⟨.privateRow 9 18, 462883235023454270145120⟩, ⟨.privateRow 9 19, 333774099514670164301952⟩, ⟨.privateRow 10 11, 4382053545314215811040⟩, ⟨.privateRow 10 12, 16857277753266169914240⟩, ⟨.privateRow 10 13, 38469817439916378804288⟩, ⟨.privateRow 10 14, 71496663107758257969600⟩, ⟨.privateRow 10 15, 141840154229907511778400⟩, ⟨.privateRow 10 16, 217652975340945185321280⟩, ⟨.privateRow 11 9, 1463641366349889896400⟩, ⟨.privateRow 11 10, 8216350397464154645700⟩, ⟨.privateRow 11 11, 21543349367513668640400⟩, ⟨.privateRow 11 12, 42725022066813604157640⟩, ⟨.privateRow 11 13, 87448875575349482194000⟩, ⟨.privateRow 11 14, 18378678520643503812750⟩, ⟨.privateRow 12 7, 582469523343323530200⟩, ⟨.privateRow 12 8, 3972740851521129718800⟩, ⟨.privateRow 12 9, 13137923693188297403400⟩, ⟨.privateRow 12 10, 29405885633029606100400⟩, ⟨.privateRow 12 11, 16037327542719507864840⟩, ⟨.privateRow 13 5, 362425481191401307680⟩, ⟨.privateRow 13 6, 1941565077811078434000⟩, ⟨.privateRow 13 7, 8363664950570799408000⟩, ⟨.privateRow 13 8, 9966700732763535961200⟩, ⟨.privateRow 14 4, 942306251097643399968⟩, ⟨.privateRow 14 5, 5048069202308803928400⟩, ⟨.hall 6 25, 69000235842209095116000⟩, ⟨.hall 5 26, 2858328961662851646569600⟩, ⟨.hall 4 27, 8911861369755962455197360⟩, ⟨.hall 3 28, 20649910393127279352488400⟩, ⟨.hall 2 29, 42215320049174424318566400⟩, ⟨.assumptionRow 18, 163502177199716550195⟩]
  caps := #[0, 0, 899457664559929455155175, 448837971408183974116500, 76593864710935787645430, 948130121363668291620, 40604815069600350726300, 16537721956905244949700, 0, 5332044745364856008490, 2365579081869954215265, 28382216135304831926980, 988532740301720926455, 0, 0, 346463002389362632693920, 95689657209961073979720, 20761991172580885497270, 3166089839399171489805] }

theorem case_50_32_18_checked :
    (Witness.linear .conditional case_50_32_18).check 50 32 18 = true := by
  change case_50_32_18.check 50 32 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_32_19 : Certificate := {
  objectiveScale := 396380001976058100000
  eta := 20739265395720588472065710400
  rows := #[⟨.count 2, 3009820396630982783837788800⟩, ⟨.count 3, 430769413275218320024121400⟩, ⟨.count 4, 58474814411864261185014240⟩, ⟨.count 5, 7208642820896972009755200⟩, ⟨.count 6, 733911599412587648052000⟩, ⟨.count 7, 57082013287645705959600⟩, ⟨.path 6, 22710775797179385458400⟩, ⟨.path 7, 49007213831047237365600⟩, ⟨.privateRow 2 30, 281985145640969787440424000⟩, ⟨.privateRow 3 27, 47615912750777793054633000⟩, ⟨.privateRow 3 28, 86636225667324270220182900⟩, ⟨.privateRow 4 24, 6723119525018911247921688⟩, ⟨.privateRow 4 25, 18403241083936975601375040⟩, ⟨.privateRow 4 26, 32032523123250515327662200⟩, ⟨.privateRow 4 27, 56656752288652745450200980⟩, ⟨.privateRow 5 21, 793556478602943977544480⟩, ⟨.privateRow 5 22, 3155548058363233335642840⟩, ⟨.privateRow 5 23, 6415692110598305088682128⟩, ⟨.privateRow 5 24, 11337711024925458182989980⟩, ⟨.privateRow 5 25, 21456313337493340217271360⟩, ⟨.privateRow 5 26, 27467049336682433054817240⟩, ⟨.privateRow 6 18, 74297223644237268074400⟩, ⟨.privateRow 6 19, 452578819637762382965400⟩, ⟨.privateRow 6 20, 1190567705713753295728800⟩, ⟨.privateRow 6 21, 2351235309229215983574000⟩, ⟨.privateRow 6 22, 4093595810056877770245600⟩, ⟨.privateRow 6 23, 7893626980348720481270400⟩, ⟨.privateRow 6 24, 11291365866518107740770400⟩, ⟨.privateRow 6 25, 12134005110288115781126400⟩, ⟨.privateRow 7 15, 5189273935240518723600⟩, ⟨.privateRow 7 16, 50558354626200482421360⟩, ⟨.privateRow 7 17, 193897632437399699608800⟩, ⟨.privateRow 7 18, 459714071298718096210350⟩, ⟨.privateRow 7 19, 900497883088778177689200⟩, ⟨.privateRow 7 20, 1572473556519192423696600⟩, ⟨.privateRow 7 21, 3048994966892961351184920⟩, ⟨.privateRow 7 22, 4573696314672612190012950⟩, ⟨.privateRow 7 23, 5575009964426730615387600⟩, ⟨.privateRow 7 24, 4389199093153614461822100⟩, ⟨.privateRow 8 12, 199587459047712258600⟩, ⟨.privateRow 8 13, 3891955451430389042700⟩, ⟨.privateRow 8 14, 25238741412306159246600⟩, ⟨.privateRow 8 15, 82249991873562221769060⟩, ⟨.privateRow 8 16, 189985084629083435491800⟩, ⟨.privateRow 8 17, 370708756748744556317175⟩, ⟨.privateRow 8 18, 650512554024793597137000⟩, ⟨.privateRow 8 19, 1273966751101547346643800⟩, ⟨.privateRow 8 20, 1991124408951787034245320⟩, ⟨.privateRow 8 21, 2592690989894544167278650⟩, ⟨.privateRow 8 22, 1414942026342248105301600⟩, ⟨.privateRow 9 10, 148264969578300534960⟩, ⟨.privateRow 9 11, 2235379541334377296320⟩, ⟨.privateRow 9 12, 12281281646735894312520⟩, ⟨.privateRow 9 13, 37362772333731734809920⟩, ⟨.privateRow 9 14, 86141947324992610811760⟩, ⟨.privateRow 9 15, 168593744296036408308960⟩, ⟨.privateRow 9 16, 297345396489281722862280⟩, ⟨.privateRow 9 17, 586832749590913517371680⟩, ⟨.privateRow 9 18, 957248065254034353880080⟩, ⟨.privateRow 9 19, 1255804292328205531111200⟩, ⟨.privateRow 10 8, 138380638273080499296⟩, ⟨.privateRow 10 9, 1334384726204704814640⟩, ⟨.privateRow 10 10, 6386798689526792275200⟩, ⟨.privateRow 10 11, 19200313560389919277320⟩, ⟨.privateRow 10 12, 44156003667137504775360⟩, ⟨.privateRow 10 13, 87179802112040714556480⟩, ⟨.privateRow 10 14, 154755680468728358379360⟩, ⟨.privateRow 10 15, 109493680033574945067960⟩, ⟨.privateRow 10 16, 914201802419801098563360⟩, ⟨.privateRow 10 17, 10032596274798336198960⟩, ⟨.privateRow 11 7, 864878989206753120600⟩, ⟨.privateRow 11 8, 3891955451430389042700⟩, ⟨.privateRow 11 9, 11576072624767310998800⟩, ⟨.privateRow 11 10, 26595028918107658458450⟩, ⟨.privateRow 11 11, 52836243704267099731200⟩, ⟨.privateRow 11 12, 26724760766488671426540⟩, ⟨.privateRow 11 13, 324906206945336922305400⟩, ⟨.privateRow 11 14, 62595616843838757103425⟩, ⟨.privateRow 12 5, 509660832925408088925⟩, ⟨.privateRow 12 6, 2718191108935509807600⟩, ⟨.privateRow 12 7, 8154573326806529422800⟩, ⟨.privateRow 12 8, 19445521010077108623600⟩, ⟨.privateRow 12 9, 39073997190947953484250⟩, ⟨.privateRow 12 10, 70796522973638505443400⟩, ⟨.privateRow 12 11, 42811509965734279469700⟩, ⟨.privateRow 13 3, 479680783929795848400⟩, ⟨.privateRow 13 4, 2548304164627040444625⟩, ⟨.privateRow 13 5, 7610935105019427461280⟩, ⟨.privateRow 13 6, 17474085700299705906000⟩, ⟨.privateRow 13 7, 34500117921104547558000⟩, ⟨.privateRow 14 1, 1177882813872054249960⟩, ⟨.privateRow 14 2, 2494340076434938411680⟩, ⟨.privateRow 14 3, 9275827159242427218435⟩, ⟨.privateRow 14 4, 8480756259878790599712⟩, ⟨.privateRow 15 0, 4122589848552189874860⟩, ⟨.hall 6 25, 654874965629693593646400⟩, ⟨.hall 5 26, 7522744904596186476411200⟩, ⟨.hall 4 27, 21996961549060613118003000⟩, ⟨.hall 3 28, 49744022062254561414172800⟩, ⟨.hall 2 29, 100327346554366092794592960⟩, ⟨.assumptionRow 19, 31157297601481133082⟩]
  caps := #[0, 15215226823634808569098500, 2292433710485646556913370, 196170936488028419127210, 174903792617795277114936, 0, 776732802765323522976, 36795176812960549346880, 1034193906716253610656, 1314376546873544062524, 20058123404472712583724, 0, 53168477183940437470305, 51666728926455350736732, 0, 401064640372950710596440, 485729591545181507443920, 135928843907487033022620, 30116215283337218969934] }

theorem case_50_32_19_checked :
    (Witness.linear .conditional case_50_32_19).check 50 32 19 = true := by
  change case_50_32_19.check 50 32 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_32_20 : Certificate := {
  objectiveScale := 1559064993781495200000
  eta := 124815454489061393909052801600
  rows := #[⟨.count 2, 12635217007100606223351446400⟩, ⟨.count 3, 1408655950115945964089857200⟩, ⟨.count 4, 180232074425609247930688800⟩, ⟨.count 5, 23714746634948585254038000⟩, ⟨.count 6, 2814497402829062865314400⟩, ⟨.count 7, 182421127961142963492600⟩, ⟨.path 3, 184006133325879275700689400⟩, ⟨.path 7, 103635551772559251244800⟩, ⟨.path 8, 10661938531766227305600⟩, ⟨.privateRow 7 17, 231645876776054556816000⟩, ⟨.privateRow 8 13, 1381978242129870935550⟩, ⟨.privateRow 8 14, 9045675766668246123600⟩, ⟨.privateRow 9 12, 4422330374815586993760⟩, ⟨.privateRow 9 13, 8442630715557029715360⟩, ⟨.privateRow 10 10, 2041075557607193997120⟩, ⟨.privateRow 10 11, 4422330374815586993760⟩, ⟨.privateRow 10 12, 4824360408889731265920⟩, ⟨.hall 13 6, 59934912832371479760⟩, ⟨.hall 11 7, 11878126421372766555⟩, ⟨.hall 12 7, 88077427992443344455⟩, ⟨.hall 10 8, 70531584925288468800⟩, ⟨.hall 11 8, 63136564158887050260⟩, ⟨.hall 14 8, 32517135108938139660⟩, ⟨.hall 10 9, 10301908491451010070⟩, ⟨.hall 9 10, 48217628262224060640⟩, ⟨.hall 13 11, 28686795885579511680⟩, ⟨.hall 8 12, 40794625457915452200⟩, ⟨.hall 7 16, 132499264494239162520⟩, ⟨.hall 6 18, 376296199462911783132⟩, ⟨.hall 5 20, 1245211037215154929920⟩, ⟨.hall 4 22, 2498586141892443534932⟩]
  caps := #[0, 146892157810136470290358800, 10651852889223133297710000, 1872994603153973699400, 0, 144612015373533976468200, 0, 70733607107782997277900, 10661938531766227305600, 43218228662970509257200, 54802923541154950812000, 67496618492429928301500, 770712643497355141440, 556290019407800146849380, 0, 95889707793158194215300, 3972497604155249769600000, 1418749144341160632000000, 425624743302348189600000] }

theorem case_50_32_20_checked :
    (Witness.linear .negative case_50_32_20).check 50 32 20 = true := by
  change case_50_32_20.check 50 32 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_33_1_checked :
    (Witness.rising).check 50 33 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_33_2_checked :
    (Witness.rising).check 50 33 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_33_3_checked :
    (Witness.rising).check 50 33 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_33_4_checked :
    (Witness.rising).check 50 33 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_33_5_checked :
    (Witness.rising).check 50 33 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_33_6_checked :
    (Witness.rising).check 50 33 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_33_7_checked :
    (Witness.rising).check 50 33 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_33_8_checked :
    (Witness.rising).check 50 33 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_33_9_checked :
    (Witness.rising).check 50 33 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_33_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_33_10_checked :
    (Witness.linear .positive case_50_33_10).check 50 33 10 = true := by
  change case_50_33_10.check 50 33 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_33_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_33_11_checked :
    (Witness.linear .positive case_50_33_11).check 50 33 11 = true := by
  change case_50_33_11.check 50 33 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_33_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_50_33_12_checked :
    (Witness.linear .positive case_50_33_12).check 50 33 12 = true := by
  change case_50_33_12.check 50 33 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_33_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_50_33_13_checked :
    (Witness.linear .positive case_50_33_13).check 50 33 13 = true := by
  change case_50_33_13.check 50 33 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_33_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_50_33_14_checked :
    (Witness.linear .positive case_50_33_14).check 50 33 14 = true := by
  change case_50_33_14.check 50 33 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_33_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_50_33_15_checked :
    (Witness.linear .positive case_50_33_15).check 50 33 15 = true := by
  change case_50_33_15.check 50 33 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_33_16 : Certificate := {
  objectiveScale := 4577567734537813400000
  eta := 851077187828084225980867896000
  rows := #[⟨.count 2, 117885691557268423193295891000⟩, ⟨.count 3, 16024786689736000290991116240⟩, ⟨.count 4, 2114001251619308309064446640⟩, ⟨.count 5, 282260031603215736762291600⟩, ⟨.count 6, 37915526633267785535233200⟩, ⟨.count 7, 6702239556385719665319000⟩, ⟨.count 8, 2144716658043430292902080⟩, ⟨.count 9, 1072358329021715146451040⟩, ⟨.path 6, 2811569023836202224394800⟩, ⟨.path 7, 999930524379455293344720⟩, ⟨.privateRow 3 27, 111815696599035089749738650⟩, ⟨.privateRow 3 28, 1818868664677637459929082040⟩, ⟨.privateRow 4 26, 1420515737406109048351271625⟩, ⟨.privateRow 4 27, 784079047988335853836942860⟩, ⟨.privateRow 5 24, 617770313944709785654066272⟩, ⟨.privateRow 5 25, 360197503016043962584715400⟩, ⟨.privateRow 5 26, 718709871515053801367864880⟩, ⟨.privateRow 5 27, 728820678617258544177260400⟩, ⟨.privateRow 6 22, 148326944468107772117000250⟩, ⟨.privateRow 6 24, 829051075411684032791233350⟩, ⟨.privateRow 6 26, 235743297539252944323232350⟩, ⟨.privateRow 8 14, 22340798521285732217730⟩, ⟨.privateRow 8 20, 52098742151638327531746360⟩, ⟨.privateRow 9 12, 9165455803604402961120⟩, ⟨.privateRow 9 21, 11378913380174866276230480⟩, ⟨.privateRow 10 19, 17827957219986014309748540⟩, ⟨.privateRow 12 16, 292558075873979826660750⟩, ⟨.hall 13 4, 565189595496481151196⟩, ⟨.hall 12 6, 15527186689463767890⟩, ⟨.hall 7 16, 186516279751331171628⟩, ⟨.hall 10 17, 338607603371741312700⟩, ⟨.hall 6 18, 637497051263015191248⟩, ⟨.hall 5 20, 1056562082062944706920⟩, ⟨.hall 11 21, 478731396884694261808500⟩, ⟨.hall 3 26, 1132058518699121387191818⟩, ⟨.hall 4 26, 3501242817001386946220160⟩, ⟨.hall 2 28, 15963009983246960850336120⟩, ⟨.assumptionRow 16, 10286579425403816049240⟩]
  caps := #[0, 0, 0, 0, 7269826385885289793943607, 0, 0, 263441014553000340231120, 0, 0, 212313084609145230868080, 79926163672124037089360, 33122626188867826646200, 10317173533963774745987280, 10286579425403816049240, 443099793930739936162920, 62954504327201198350760, 4577567734537813400000] }

theorem case_50_33_16_checked :
    (Witness.linear .conditional case_50_33_16).check 50 33 16 = true := by
  change case_50_33_16.check 50 33 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_33_17 : Certificate := {
  objectiveScale := 424249325992800000
  eta := 27516464103699575052048000
  rows := #[⟨.count 2, 3942907966078902522702000⟩, ⟨.count 3, 563751947490430318139520⟩, ⟨.count 4, 78618468867713071577280⟩, ⟨.count 5, 10693881787822134501600⟩, ⟨.count 6, 1475018177630639241600⟩, ⟨.count 7, 234661982804874424800⟩, ⟨.count 8, 93864793121949769920⟩, ⟨.path 7, 57702230141108913360⟩, ⟨.privateRow 2 31, 327177469525696166777400⟩, ⟨.privateRow 3 27, 8109527022431785330380⟩, ⟨.privateRow 3 28, 64503364362330982168080⟩, ⟨.privateRow 3 29, 104025656977400832513840⟩, ⟨.privateRow 4 24, 1557987950122362698940⟩, ⟨.privateRow 4 25, 12607717873297888917576⟩, ⟨.privateRow 4 26, 25886569017417718690080⟩, ⟨.privateRow 4 27, 39309234433856535788640⟩, ⟨.privateRow 4 28, 61240910962502103012180⟩, ⟨.privateRow 5 21, 101407499712106447860⟩, ⟨.privateRow 5 22, 2180919734068159450080⟩, ⟨.privateRow 5 23, 5678819983877961080160⟩, ⟨.privateRow 5 24, 9646618881704380640064⟩, ⟨.privateRow 5 25, 14547366776882179520280⟩, ⟨.privateRow 5 26, 23501956296914851916160⟩, ⟨.privateRow 5 27, 24153422658701717581200⟩, ⟨.privateRow 6 19, 239007575079038766000⟩, ⟨.privateRow 6 20, 1136993178590284415400⟩, ⟨.privateRow 6 21, 2313495772652818096200⟩, ⟨.privateRow 6 22, 3825828398229470532900⟩, ⟨.privateRow 6 23, 5605069074996429118080⟩, ⟨.privateRow 6 24, 9042168724329491600850⟩, ⟨.privateRow 6 25, 10069047698686933156200⟩, ⟨.privateRow 6 26, 7252172706683976271200⟩, ⟨.privateRow 7 16, 3047558218245122400⟩, ⟨.privateRow 7 17, 164263387963412097360⟩, ⟨.privateRow 7 18, 519608676210793369200⟩, ⟨.privateRow 7 19, 1001503819470803348700⟩, ⟨.privateRow 7 20, 1625872309433772800400⟩, ⟨.privateRow 7 21, 2363381398249092421200⟩, ⟨.privateRow 7 22, 3768000981038269335360⟩, ⟨.privateRow 7 23, 4387340999941134335100⟩, ⟨.privateRow 7 24, 910711980885584077200⟩, ⟨.privateRow 8 14, 977758261686976770⟩, ⟨.privateRow 8 15, 90664856992792391400⟩, ⟨.privateRow 8 16, 248741701773166890288⟩, ⟨.privateRow 8 17, 477146031703244663760⟩, ⟨.privateRow 8 18, 769984631078494206375⟩, ⟨.privateRow 8 19, 1112968261303118700480⟩, ⟨.privateRow 8 20, 1773653486700175860780⟩, ⟨.privateRow 8 21, 894062154486571558488⟩, ⟨.privateRow 9 13, 47801515015807753200⟩, ⟨.privateRow 9 14, 133686220507019369280⟩, ⟨.privateRow 9 15, 257606710012462146336⟩, ⟨.privateRow 9 16, 418335682926220579520⟩, ⟨.privateRow 9 17, 607513799928174899760⟩, ⟨.privateRow 9 18, 414197023617492635520⟩, ⟨.privateRow 10 11, 25271290455909553440⟩, ⟨.privateRow 10 12, 81153935720019071910⟩, ⟨.privateRow 10 13, 162130097210640511680⟩, ⟨.privateRow 10 14, 267514660397556844272⟩, ⟨.privateRow 10 15, 91257437757451165200⟩, ⟨.privateRow 11 9, 15564315186037589400⟩, ⟨.privateRow 11 10, 55442116816536265200⟩, ⟨.privateRow 11 11, 120124586435828574600⟩, ⟨.privateRow 11 12, 9142674654735367200⟩, ⟨.privateRow 12 7, 10243181789101661400⟩, ⟨.privateRow 12 8, 43899350524721406000⟩, ⟨.privateRow 12 9, 7091433546301150200⟩, ⟨.privateRow 13 5, 9218863610191495260⟩, ⟨.privateRow 13 6, 9833454517537594944⟩, ⟨.hall 5 27, 447773375352158341200⟩, ⟨.hall 4 28, 11967992317120324605120⟩, ⟨.hall 3 29, 38702018617398589300848⟩, ⟨.hall 2 30, 95798862044744783324400⟩, ⟨.assumptionRow 17, 424279966221899480⟩]
  caps := #[0, 5656045282418668903920, 12364606976203877277960, 0, 0, 268866627288494472424, 0, 0, 92612476057013413907, 23338768567405414200, 20010463985877428910, 92313869060001145080, 117523014911978813280, 424279966221899480, 894717377615993814960, 223999507693269970200, 43697190333592808320, 5939459923670100520] }

theorem case_50_33_17_checked :
    (Witness.linear .conditional case_50_33_17).check 50 33 17 = true := by
  change case_50_33_17.check 50 33 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_33_18 : Certificate := {
  objectiveScale := 27759154069336258800000
  eta := 1999648023293372667890183308800
  rows := #[⟨.count 2, 270657880453435794388510240800⟩, ⟨.count 3, 35729907164674526964602201760⟩, ⟨.count 4, 4468976739174496321752819840⟩, ⟨.count 5, 539243045450919616501094400⟩, ⟨.count 6, 58979708096194333054807200⟩, ⟨.count 7, 10723583290217151464510400⟩, ⟨.count 8, 4289433316086860585804160⟩, ⟨.path 6, 8831067922036239924844800⟩, ⟨.path 7, 1920234115730225019684960⟩, ⟨.privateRow 2 31, 23385454260141053056231054800⟩, ⟨.privateRow 3 27, 460041723150315797827496160⟩, ⟨.privateRow 3 28, 4361877078758549786808852480⟩, ⟨.privateRow 3 29, 7437341190930105398211187920⟩, ⟨.privateRow 4 24, 71196933344691730616160120⟩, ⟨.privateRow 4 25, 773308229866959412538600688⟩, ⟨.privateRow 4 26, 1727894805403864693030655220⟩, ⟨.privateRow 4 27, 2800412711557874737568964720⟩, ⟨.privateRow 4 28, 4638754041765684294760586280⟩, ⟨.privateRow 5 22, 114107680153453525991749440⟩, ⟨.privateRow 5 23, 342082306957927131717881760⟩, ⟨.privateRow 5 24, 632262470791203250347533184⟩, ⟨.privateRow 5 25, 1029617189907849642756777120⟩, ⟨.privateRow 5 26, 1798600241181088137538025280⟩, ⟨.privateRow 5 27, 2044068169162392171299460960⟩, ⟨.privateRow 6 19, 7489486742373883562515200⟩, ⟨.privateRow 6 20, 58277568714096781470821400⟩, ⟨.privateRow 6 21, 135211983866785647887551200⟩, ⟨.privateRow 6 22, 245514737273443870533701400⟩, ⟨.privateRow 6 23, 393198053974628887032048000⟩, ⟨.privateRow 6 24, 694064779203429740769963300⟩, ⟨.privateRow 6 25, 871120926722362331865049200⟩, ⟨.privateRow 6 26, 761821229575843468624593000⟩, ⟨.privateRow 7 17, 5132000574603922486587120⟩, ⟨.privateRow 7 18, 25447233363293081649909600⟩, ⟨.privateRow 7 19, 56298812273640045188679600⟩, ⟨.privateRow 7 20, 101545768299199148561894400⟩, ⟨.privateRow 7 21, 162641013234960130545074400⟩, ⟨.privateRow 7 22, 286932450036810352757542560⟩, ⟨.privateRow 7 23, 378772281215170099942885200⟩, ⟨.privateRow 7 24, 335750286348465575615028000⟩, ⟨.privateRow 8 15, 2534665141324053982520640⟩, ⟨.privateRow 8 16, 11313380371179094795058472⟩, ⟨.privateRow 8 17, 25557873508350877657083120⟩, ⟨.privateRow 8 18, 46178430543497608494047910⟩, ⟨.privateRow 8 19, 74145918749501447268900480⟩, ⟨.privateRow 8 20, 76226804554626918326894760⟩, ⟨.privateRow 8 21, 292646587990026063466488816⟩, ⟨.privateRow 9 13, 1151792279319619972114080⟩, ⟨.privateRow 9 14, 5415951156675329022480000⟩, ⟨.privateRow 9 15, 12820639578081838862014656⟩, ⟨.privateRow 9 16, 23724273155640907931361280⟩, ⟨.privateRow 9 17, 21745043894051446025257200⟩, ⟨.privateRow 9 18, 101925105939397306300775040⟩, ⟨.privateRow 9 19, 34236032578396979860770240⟩, ⟨.privateRow 10 11, 536179164510857573225520⟩, ⟨.privateRow 10 12, 2859622210724573723869440⟩, ⟨.privateRow 10 13, 7311534061511694180348000⟩, ⟨.privateRow 10 14, 14101512026635554175831176⟩, ⟨.privateRow 10 15, 23353581387584018744933760⟩, ⟨.privateRow 10 16, 25401487918701877531559010⟩, ⟨.privateRow 11 9, 273560798219825292462000⟩, ⟨.privateRow 11 10, 1708702831957677980608800⟩, ⟨.privateRow 11 11, 4787313968846942618085000⟩, ⟨.privateRow 11 12, 9818345739744275042181600⟩, ⟨.privateRow 11 13, 9268239843687680908612560⟩, ⟨.privateRow 12 7, 187237168559347089062880⟩, ⟨.privateRow 12 8, 1103361886153295346263400⟩, ⟨.privateRow 12 9, 3672729075587192900848800⟩, ⟨.privateRow 12 10, 3744743371186941781257600⟩, ⟨.privateRow 13 5, 210641814629265475195740⟩, ⟨.privateRow 13 6, 898738409084866027501824⟩, ⟨.privateRow 13 7, 1685134517034123801565920⟩, ⟨.privateRow 14 4, 684585897545112794386155⟩, ⟨.hall 5 27, 196799638239342315397162800⟩, ⟨.hall 4 28, 1149726605311626673716665280⟩, ⟨.hall 3 29, 3164064740333838653946890256⟩, ⟨.hall 2 30, 7222160384940441557291875200⟩, ⟨.assumptionRow 18, 20253960051974062555680⟩]
  caps := #[0, 0, 0, 40003193279076889452051384, 0, 2379533297188677649642656, 2119985898838757788829760, 2520852046043974772912640, 0, 7028068865050666117166048, 901983069653177402060184, 239944941030908804042880, 1347303704748695407505880, 0, 11863076092387278752759535, 48863166217131761272784160, 12690758567534011343074080, 2583142622431359976864800] }

theorem case_50_33_18_checked :
    (Witness.linear .conditional case_50_33_18).check 50 33 18 = true := by
  change case_50_33_18.check 50 33 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_33_19 : Certificate := {
  objectiveScale := 7532095225673578560000
  eta := 657348506634784573340177846400
  rows := #[⟨.count 2, 92519502100230177118640894400⟩, ⟨.count 3, 12651147386633684440256144400⟩, ⟨.count 4, 1643006154108270706526772000⟩, ⟨.count 5, 196599026987314443516024000⟩, ⟨.count 6, 19659902698731444351602400⟩, ⟨.count 7, 893631940851429288709200⟩, ⟨.path 6, 795191239064784467505600⟩, ⟨.path 7, 1192362279198778746938880⟩, ⟨.privateRow 2 31, 8434098257755789626837429600⟩, ⟨.privateRow 3 27, 95842025656315791214061700⟩, ⟨.privateRow 3 28, 1522113355608452269355172480⟩, ⟨.privateRow 3 29, 2658018844868491276336644480⟩, ⟨.privateRow 4 24, 12474676355266499808814380⟩, ⟨.privateRow 4 25, 253022947732673688805122888⟩, ⟨.privateRow 4 26, 599697246249518807882271780⟩, ⟨.privateRow 4 27, 996757066825684228626241680⟩, ⟨.privateRow 4 28, 1701424150698786998314390560⟩, ⟨.privateRow 5 22, 35468069358527748585339840⟩, ⟨.privateRow 5 23, 113465724146964335972105280⟩, ⟨.privateRow 5 24, 216146587384910279614188672⟩, ⟨.privateRow 5 25, 363146488420853679237455760⟩, ⟨.privateRow 5 26, 658138647486105018056023200⟩, ⟨.privateRow 5 27, 784710973432223650262530080⟩, ⟨.privateRow 6 19, 3328660774388392694451200⟩, ⟨.privateRow 6 20, 18548182010410321010291550⟩, ⟨.privateRow 6 21, 44134475446131813850536000⟩, ⟨.privateRow 6 22, 82345346422662855210779100⟩, ⟨.privateRow 6 23, 136355468003344517610042360⟩, ⟨.privateRow 6 24, 251541433636447854962912850⟩, ⟨.privateRow 6 25, 334764454286732649653674200⟩, ⟨.privateRow 6 26, 318771279472288419129553200⟩, ⟨.privateRow 7 16, 220506582807495538772400⟩, ⟨.privateRow 7 17, 2195781340377797680828320⟩, ⟨.privateRow 7 18, 8127795271553475911593200⟩, ⟨.privateRow 7 19, 17984342809635014435272650⟩, ⟨.privateRow 7 20, 33283230450078743916210000⟩, ⟨.privateRow 7 21, 55192410823062085116944400⟩, ⟨.privateRow 7 22, 102231494033403510628332480⟩, ⟨.privateRow 7 23, 114257226723147030484962000⟩, ⟨.privateRow 7 24, 216939792117170786373309600⟩, ⟨.privateRow 8 14, 171279455329857280335930⟩, ⟨.privateRow 8 15, 1153597596371845081788240⟩, ⟨.privateRow 8 16, 3654954638082345790820628⟩, ⟨.privateRow 8 17, 7993041248726673082343400⟩, ⟨.privateRow 8 18, 14733756624787940397592935⟩, ⟨.privateRow 8 19, 24511047520496346204595200⟩, ⟨.privateRow 8 20, 45768849237274036736722860⟩, ⟨.privateRow 8 21, 67612192644819139983738072⟩, ⟨.privateRow 8 22, 56276471475118759456461870⟩, ⟨.privateRow 9 12, 103875165774183233559360⟩, ⟨.privateRow 9 13, 608993618950603663416640⟩, ⟨.privateRow 9 14, 1812538320434010112856640⟩, ⟨.privateRow 9 15, 3979640909925031765718304⟩, ⟨.privateRow 9 16, 7387357377705148786662720⟩, ⟨.privateRow 9 17, 12332120783749724184186960⟩, ⟨.privateRow 9 18, 21186169315169758501842240⟩, ⟨.privateRow 9 19, 39716975148952412831520000⟩, ⟨.privateRow 10 10, 63830852917959234907800⟩, ⟨.privateRow 10 11, 350578684487868413262840⟩, ⟨.privateRow 10 12, 1042570597660000836827400⟩, ⟨.privateRow 10 13, 2307195192743690163576480⟩, ⟨.privateRow 10 14, 4325178593720917757352528⟩, ⟨.privateRow 10 15, 2591532628469144937256680⟩, ⟨.privateRow 10 16, 23055704073966875648697360⟩, ⟨.privateRow 11 8, 42553901945306156605200⟩, ⟨.privateRow 11 9, 237086025123848586800400⟩, ⟨.privateRow 11 10, 716869578924772945887600⟩, ⟨.privateRow 11 11, 1606409798435307411846300⟩, ⟨.privateRow 11 12, 1473912421923785969689200⟩, ⟨.privateRow 11 13, 8387374073419843466884920⟩, ⟨.privateRow 12 6, 29255807587397982666075⟩, ⟨.privateRow 12 7, 187237168559347089062880⟩, ⟨.privateRow 12 8, 601833756083615643416400⟩, ⟨.privateRow 12 9, 1386275190295165947869400⟩, ⟨.privateRow 12 10, 2203937504917314694177650⟩, ⟨.privateRow 13 4, 33041853275178898069920⟩, ⟨.privateRow 13 5, 210641814629265475195740⟩, ⟨.privateRow 13 6, 636606373101780102813792⟩, ⟨.privateRow 13 7, 641956006489190019644160⟩, ⟨.privateRow 14 3, 214772046288662837454480⟩, ⟨.privateRow 14 4, 228195299181704264795385⟩, ⟨.hall 5 27, 105421212940646673538439400⟩, ⟨.hall 4 28, 467595774433572214868998560⟩, ⟨.hall 3 29, 1205479700477216396159087160⟩, ⟨.hall 2 30, 2646476579413107009007639200⟩, ⟨.assumptionRow 19, 2293368778694997247860⟩]
  caps := #[0, 241386004018586395831331700, 7409885950828944605622600, 18900605030871893661490620, 0, 0, 0, 1488151281834503810784780, 324262246375327664394585, 185531135963928700716512, 903235078295811874758432, 0, 1430894475273824634790695, 0, 2526491064110805029745045, 36340460963618496884282160, 11556969268035005049164160, 3075611546312094852622560] }

theorem case_50_33_19_checked :
    (Witness.linear .conditional case_50_33_19).check 50 33 19 = true := by
  change case_50_33_19.check 50 33 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_33_20 : Certificate := {
  objectiveScale := 1290504322016624000000
  eta := 164229948479467575138417984000
  rows := #[⟨.count 2, 21889081988603735541792156000⟩, ⟨.count 3, 2778388184617498635624842400⟩, ⟨.count 4, 325067884253679365592393600⟩, ⟨.count 5, 33521493080786333687064000⟩, ⟨.count 6, 2717958898442135163816000⟩, ⟨.path 6, 868321429153090632720000⟩, ⟨.path 7, 121515046681492862798400⟩, ⟨.privateRow 6 20, 2784020399445937060158750⟩, ⟨.privateRow 6 22, 16005757957492573742472000⟩, ⟨.privateRow 7 17, 226496574870177930318000⟩, ⟨.privateRow 7 18, 1162224848828791804056000⟩, ⟨.privateRow 7 19, 1642100167808789994805500⟩, ⟨.privateRow 7 20, 4006342012638731702508000⟩, ⟨.privateRow 7 22, 30037563947328687704354400⟩, ⟨.privateRow 8 13, 2217448984743000716400⟩, ⟨.privateRow 8 14, 7206709200414752328300⟩, ⟨.privateRow 8 15, 115307347206636037252800⟩, ⟨.privateRow 8 17, 1819293700371368587766400⟩, ⟨.privateRow 8 18, 1026956061059102206782750⟩, ⟨.privateRow 9 12, 3942131528432001273600⟩, ⟨.privateRow 9 13, 57653673603318018626400⟩, ⟨.privateRow 9 14, 60565475300455292294400⟩, ⟨.privateRow 9 15, 479166087280909754806080⟩, ⟨.privateRow 9 16, 153743129608848049670400⟩, ⟨.privateRow 9 21, 21940425787929357088380000⟩, ⟨.privateRow 10 10, 2059059771547072093800⟩, ⟨.privateRow 10 11, 31044285786402010029600⟩, ⟨.privateRow 10 12, 31229073201797260089300⟩, ⟨.privateRow 10 14, 807151430446452260769600⟩, ⟨.privateRow 10 16, 147737538608502422730150⟩, ⟨.privateRow 10 18, 461229388826544149011200⟩, ⟨.privateRow 11 9, 2941513959352960134000⟩, ⟨.privateRow 11 10, 53852332486615731684000⟩, ⟨.hall 11 6, 176065851024222588000⟩, ⟨.hall 10 7, 37795245381375300000⟩, ⟨.hall 11 7, 34087461818267232375⟩, ⟨.hall 12 7, 77914198441753674000⟩, ⟨.hall 10 8, 64755853753423014000⟩, ⟨.hall 13 8, 28049111439031322640⟩, ⟨.hall 9 10, 38935401950380121550⟩, ⟨.hall 8 11, 13595463032445133840⟩, ⟨.hall 7 13, 29249236464041259666⟩, ⟨.hall 6 17, 51988282470140890720⟩, ⟨.hall 5 20, 481325398278862918000⟩, ⟨.hall 4 23, 8882170005947098037320⟩, ⟨.hall 3 26, 354387591066350429107520⟩]
  caps := #[0, 0, 0, 0, 357823873408387664678400, 4190991555341905142400, 488881256383558161530550, 196070361828699259747560, 122359167292006204560, 29173526263209756964480, 342447744897119640397850, 15410909317085701848000, 0, 0, 331857341830491755129280, 12899881202878173504000000, 4914240458239304192000000, 1626035445740946240000000] }

theorem case_50_33_20_checked :
    (Witness.linear .negative case_50_33_20).check 50 33 20 = true := by
  change case_50_33_20.check 50 33 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_33_21 : Certificate := {
  objectiveScale := 9030911876800000
  eta := 1132397925363527462640000
  rows := #[⟨.count 2, 136402477373333989818000⟩, ⟨.count 3, 15074128227241761678000⟩, ⟨.count 4, 1470646656316269432000⟩, ⟨.count 5, 113126665870482264000⟩, ⟨.count 6, 4040238066802938000⟩, ⟨.path 5, 19278737429215992000⟩, ⟨.path 6, 5243553513139032000⟩, ⟨.hall 14 6, 903390004617100⟩, ⟨.hall 13 8, 166779693160080⟩, ⟨.hall 12 10, 219929265705600⟩, ⟨.hall 11 11, 216683781749875⟩, ⟨.hall 9 12, 142617174525000⟩, ⟨.hall 10 12, 203738820750000⟩, ⟨.hall 13 12, 125084769870060⟩, ⟨.hall 8 13, 53747447887952⟩]
  caps := #[0, 1046438883552660312000, 0, 28080877256987282000, 0, 0, 1203315446336094000, 0, 0, 0, 0, 0, 1619998838379922000, 0, 36340728502984173840, 0, 55883282693638400000, 23010763462086400000] }

theorem case_50_33_21_checked :
    (Witness.linear .negative case_50_33_21).check 50 33 21 = true := by
  change case_50_33_21.check 50 33 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_34_1_checked :
    (Witness.rising).check 50 34 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_34_2_checked :
    (Witness.rising).check 50 34 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_34_3_checked :
    (Witness.rising).check 50 34 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_34_4_checked :
    (Witness.rising).check 50 34 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_34_5_checked :
    (Witness.rising).check 50 34 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_34_6_checked :
    (Witness.rising).check 50 34 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_34_7_checked :
    (Witness.rising).check 50 34 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_34_8_checked :
    (Witness.rising).check 50 34 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_34_9_checked :
    (Witness.rising).check 50 34 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_34_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_34_10_checked :
    (Witness.linear .positive case_50_34_10).check 50 34 10 = true := by
  change case_50_34_10.check 50 34 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_34_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_50_34_11_checked :
    (Witness.linear .positive case_50_34_11).check 50 34 11 = true := by
  change case_50_34_11.check 50 34 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_34_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_50_34_12_checked :
    (Witness.linear .positive case_50_34_12).check 50 34 12 = true := by
  change case_50_34_12.check 50 34 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_34_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_50_34_13_checked :
    (Witness.linear .positive case_50_34_13).check 50 34 13 = true := by
  change case_50_34_13.check 50 34 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_34_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_50_34_14_checked :
    (Witness.linear .positive case_50_34_14).check 50 34 14 = true := by
  change case_50_34_14.check 50 34 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_34_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_50_34_15_checked :
    (Witness.linear .positive case_50_34_15).check 50 34 15 = true := by
  change case_50_34_15.check 50 34 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_34_16 : Certificate := {
  objectiveScale := 7
  eta := 17866745
  rows := #[⟨.assumptionRow 16, 18⟩]
  caps := #[0, 0, 5051720, 1456084, 425068, 125970, 38012, 11726, 3718, 1221, 420, 24794, 29183, 12425, 3590, 740, 101] }

theorem case_50_34_16_checked :
    (Witness.linear .conditional case_50_34_16).check 50 34 16 = true := by
  change case_50_34_16.check 50 34 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_34_17 : Certificate := {
  objectiveScale := 74827284586560000
  eta := 10756585831188860614551600
  rows := #[⟨.count 2, 1300172991433419912288480⟩, ⟨.count 3, 153186803114394098649600⟩, ⟨.count 4, 17086220347374726387840⟩, ⟨.count 5, 1841187537432621378000⟩, ⟨.count 6, 133904548176917918400⟩, ⟨.path 6, 78844339879905600000⟩, ⟨.privateRow 2 31, 20105767908764225447760⟩, ⟨.privateRow 2 32, 109464736392160782993360⟩, ⟨.privateRow 3 28, 10930516680558328914060⟩, ⟨.privateRow 3 29, 24573716332934053325040⟩, ⟨.privateRow 3 30, 33828752354428696785120⟩, ⟨.privateRow 4 24, 147295002994609710240⟩, ⟨.privateRow 4 25, 2307621713582218793760⟩, ⟨.privateRow 4 26, 6024365622479537148816⟩, ⟨.privateRow 4 27, 9150702061040128248660⟩, ⟨.privateRow 4 28, 12667370257536435080640⟩, ⟨.privateRow 4 29, 18190932869834299214640⟩, ⟨.privateRow 5 21, 51826019572177490640⟩, ⟨.privateRow 5 22, 383580736965129453750⟩, ⟨.privateRow 5 23, 1322148003070663351440⟩, ⟨.privateRow 5 24, 2364903103635678125520⟩, ⟨.privateRow 5 25, 3471252237239635504656⟩, ⟨.privateRow 5 26, 4688890928661742442640⟩, ⟨.privateRow 5 27, 6963780419356270189680⟩, ⟨.privateRow 5 28, 6014545955613229834800⟩, ⟨.privateRow 6 12, 2625579376017998400⟩, ⟨.privateRow 6 19, 60257046679613063280⟩, ⟨.privateRow 6 20, 254170670150631234000⟩, ⟨.privateRow 6 21, 595596271578582824550⟩, ⟨.privateRow 6 22, 970807974282654908400⟩, ⟨.privateRow 6 23, 1413436897423022472000⟩, ⟨.privateRow 6 24, 1872431932007235558960⟩, ⟨.privateRow 6 25, 2747832915713836450500⟩, ⟨.privateRow 6 26, 2328451309965294914400⟩, ⟨.privateRow 7 15, 1545052478964437520⟩, ⟨.privateRow 7 17, 44431963713250036560⟩, ⟨.privateRow 7 18, 137921684622225455952⟩, ⟨.privateRow 7 19, 278967808701912330000⟩, ⟨.privateRow 7 20, 445232622688252078680⟩, ⟨.privateRow 7 21, 637959525957173225520⟩, ⟨.privateRow 7 22, 750981341025547992360⟩, ⟨.privateRow 7 23, 1392607301039946351360⟩, ⟨.privateRow 8 14, 400569161213002320⟩, ⟨.privateRow 8 15, 29508594876024504240⟩, ⟨.privateRow 8 16, 78110986436535452400⟩, ⟨.privateRow 8 17, 147890134319840456544⟩, ⟨.privateRow 8 18, 234332959309606357200⟩, ⟨.privateRow 8 19, 304632847102488264360⟩, ⟨.privateRow 8 20, 490983343315365700800⟩, ⟨.privateRow 9 13, 20028458060650116000⟩, ⟨.privateRow 9 14, 50338191259100624880⟩, ⟨.privateRow 9 15, 93259783806045358320⟩, ⟨.privateRow 9 16, 146848654500686650512⟩, ⟨.privateRow 9 17, 125556178197986616080⟩, ⟨.privateRow 10 11, 14346915876098348400⟩, ⟨.privateRow 10 12, 38626311974110938000⟩, ⟨.privateRow 10 13, 71415759027689556480⟩, ⟨.privateRow 10 14, 17042397040698644160⟩, ⟨.privateRow 11 9, 11902626504614926080⟩, ⟨.privateRow 11 10, 32679086162224015800⟩, ⟨.privateRow 12 7, 12274583582884142520⟩, ⟨.privateRow 12 8, 1636611144384552336⟩, ⟨.privateRow 13 5, 4332205970429697360⟩, ⟨.hall 4 29, 1423851695614560532320⟩, ⟨.hall 3 30, 8369682186290484018960⟩, ⟨.hall 2 31, 25830326827231817415525⟩, ⟨.assumptionRow 17, 78769263346115760⟩]
  caps := #[0, 0, 2059425000307048682880, 0, 69295715634261346560, 77048718521127650220, 0, 20367684975072093120, 70099387094735929128, 4765927147587500400, 89564507026605060480, 43845832444920192720, 240249768797903040, 78769263346115760, 202404289214394828000, 47739245071465284480, 8762605942301632080] }

theorem case_50_34_17_checked :
    (Witness.linear .conditional case_50_34_17).check 50 34 17 = true := by
  change case_50_34_17.check 50 34 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_34_18 : Certificate := {
  objectiveScale := 3288555441600000
  eta := 320074581076304048794800
  rows := #[⟨.count 2, 39749334256407434218560⟩, ⟨.count 3, 4853116391770675108080⟩, ⟨.count 4, 548546907704063748480⟩, ⟨.count 5, 59256610400130343200⟩, ⟨.count 6, 6926097319495754400⟩, ⟨.count 7, 1616089374549009360⟩, ⟨.path 6, 2471362239683937600⟩, ⟨.privateRow 2 31, 2580625382925676446360⟩, ⟨.privateRow 2 32, 5469385139932030677360⟩, ⟨.privateRow 3 28, 566747152326960925320⟩, ⟨.privateRow 3 29, 1250878828113227673360⟩, ⟨.privateRow 3 30, 1661724660220798052880⟩, ⟨.privateRow 4 24, 4353546886540188480⟩, ⟨.privateRow 4 25, 88461654097337440920⟩, ⟨.privateRow 4 26, 270210143424594364992⟩, ⟨.privateRow 4 27, 429822056152374025140⟩, ⟨.privateRow 4 28, 634045731281394672240⟩, ⟨.privateRow 4 29, 962496657499260003120⟩, ⟨.privateRow 5 22, 12380398958598660990⟩, ⟨.privateRow 5 23, 49823925479293268160⟩, ⟨.privateRow 5 24, 101864935021176447120⟩, ⟨.privateRow 5 25, 161008675687211303952⟩, ⟨.privateRow 5 26, 234910134086231003400⟩, ⟨.privateRow 5 27, 379806655231311628320⟩, ⟨.privateRow 5 28, 373316645520821162160⟩, ⟨.privateRow 6 19, 692609731949575440⟩, ⟨.privateRow 6 20, 7994939498430284400⟩, ⟨.privateRow 6 21, 22125033103944771000⟩, ⟨.privateRow 6 22, 40622110469106051600⟩, ⟨.privateRow 6 23, 64835966574168589800⟩, ⟨.privateRow 6 24, 93810140360725829040⟩, ⟨.privateRow 6 25, 151700770456177842900⟩, ⟨.privateRow 6 26, 166867640975258823600⟩, ⟨.privateRow 6 27, 69453364787165759400⟩, ⟨.privateRow 7 17, 503716168690600320⟩, ⟨.privateRow 7 18, 4248006355957396032⟩, ⟨.privateRow 7 19, 10081319431710486960⟩, ⟨.privateRow 7 20, 18065570508351426060⟩, ⟨.privateRow 7 21, 28627868920582451520⟩, ⟨.privateRow 7 22, 41441148961649597160⟩, ⟨.privateRow 7 23, 66998448070588930896⟩, ⟨.privateRow 7 24, 66201946878846919140⟩, ⟨.privateRow 8 15, 299275810101668400⟩, ⟨.privateRow 8 16, 2252730643310740320⟩, ⟨.privateRow 8 17, 5135572901344629744⟩, ⟨.privateRow 8 18, 9157839789111053040⟩, ⟨.privateRow 8 19, 14410130256395333460⟩, ⟨.privateRow 8 20, 20829596383076120640⟩, ⟨.privateRow 8 21, 33818166541488529200⟩, ⟨.privateRow 8 22, 2980787068612617264⟩, ⟨.privateRow 9 13, 165752756364000960⟩, ⟨.privateRow 9 14, 1286885983437174120⟩, ⟨.privateRow 9 15, 3036289127940563040⟩, ⟨.privateRow 9 16, 5440834227648331512⟩, ⟨.privateRow 9 17, 8579239889581160800⟩, ⟨.privateRow 9 18, 12412464223966696890⟩, ⟨.privateRow 9 19, 1513480525371294480⟩, ⟨.privateRow 10 11, 115434955324929240⟩, ⟨.privateRow 10 12, 834683523118719120⟩, ⟨.privateRow 10 13, 2135546673511190940⟩, ⟨.privateRow 10 14, 3924788481047594160⟩, ⟨.privateRow 10 15, 4478876266607254512⟩, ⟨.privateRow 11 9, 76956636883286160⟩, ⟨.privateRow 11 10, 632143802969850600⟩, ⟨.privateRow 11 11, 1805521096107867600⟩, ⟨.privateRow 11 12, 1442936941561615500⟩, ⟨.privateRow 12 7, 105815375714518470⟩, ⟨.privateRow 12 8, 620783537525175024⟩, ⟨.privateRow 12 9, 604659289797248400⟩, ⟨.privateRow 13 5, 149386412773437840⟩, ⟨.privateRow 13 6, 317446127143555410⟩, ⟨.hall 4 29, 123930968036844032064⟩, ⟨.hall 3 30, 490956036121632921840⟩, ⟨.hall 2 31, 1343273287007954717415⟩, ⟨.assumptionRow 18, 2640887095667040⟩]
  caps := #[0, 0, 46105058769470201160, 0, 174437108378110116, 0, 0, 69492485255849292, 448921032188360160, 1367859445260381536, 490488152257520868, 3590604990113031000, 78384652557894210, 0, 25268225762568016800, 7452402766388902080, 1823792499865749600] }

theorem case_50_34_18_checked :
    (Witness.linear .conditional case_50_34_18).check 50 34 18 = true := by
  change case_50_34_18.check 50 34 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_34_19 : Certificate := {
  objectiveScale := 6042720623940000
  eta := 694457845584327557132400
  rows := #[⟨.count 2, 85815423181468763022240⟩, ⟨.count 3, 10267477536331156181040⟩, ⟨.count 4, 1107252091476721270080⟩, ⟨.count 5, 101582760685937731200⟩, ⟨.count 6, 4617398212997169600⟩, ⟨.path 6, 5462009614438977600⟩, ⟨.privateRow 2 31, 5854553107532877908160⟩, ⟨.privateRow 2 32, 12633509337307789170240⟩, ⟨.privateRow 3 28, 1218781497479823737460⟩, ⟨.privateRow 3 29, 2780545899442306675680⟩, ⟨.privateRow 3 30, 3802158080174077664040⟩, ⟨.privateRow 4 24, 13060640659620565440⟩, ⟨.privateRow 4 25, 182002446228971768400⟩, ⟨.privateRow 4 26, 573942597875548181280⟩, ⟨.privateRow 4 27, 945354566633508010980⟩, ⟨.privateRow 4 28, 1445861293763180374080⟩, ⟨.privateRow 4 29, 2280532977399302065440⟩, ⟨.privateRow 5 21, 3009859575879636480⟩, ⟨.privateRow 5 22, 25078244044340877390⟩, ⟨.privateRow 5 23, 100615305822262133760⟩, ⟨.privateRow 5 24, 212618361602372445720⟩, ⟨.privateRow 5 25, 348259564551623188464⟩, ⟨.privateRow 5 26, 531193186086882719400⟩, ⟨.privateRow 5 27, 903522221434368375840⟩, ⟨.privateRow 5 28, 956147734956388894920⟩, ⟨.privateRow 6 18, 314822605431625200⟩, ⟨.privateRow 6 19, 3039787156889803320⟩, ⟨.privateRow 6 20, 15690603186758900400⟩, ⟨.privateRow 6 21, 43672891431264895800⟩, ⟨.privateRow 6 22, 82948260754913439600⟩, ⟨.privateRow 6 23, 137752380021082226400⟩, ⟨.privateRow 6 24, 209245095685655069040⟩, ⟨.privateRow 6 25, 358906515264425828700⟩, ⟨.privateRow 6 26, 430187600177569634400⟩, ⟨.privateRow 6 27, 298014576330525654600⟩, ⟨.privateRow 7 16, 230869910649858480⟩, ⟨.privateRow 7 17, 2056841022153284640⟩, ⟨.privateRow 7 18, 8080446872745046800⟩, ⟨.privateRow 7 19, 19444376919176969760⟩, ⟨.privateRow 7 20, 35986847322546690570⟩, ⟨.privateRow 7 21, 59465492700242119920⟩, ⟨.privateRow 7 22, 90616439930069453400⟩, ⟨.privateRow 7 23, 98073538044059882304⟩, ⟨.privateRow 7 24, 316349495067968582220⟩, ⟨.privateRow 8 14, 138127296970000800⟩, ⟨.privateRow 8 15, 1271922192932090700⟩, ⟨.privateRow 8 16, 4309571665464024960⟩, ⟨.privateRow 8 17, 9678579698687956056⟩, ⟨.privateRow 8 18, 17757031399365658400⟩, ⟨.privateRow 8 19, 29134500113397418740⟩, ⟨.privateRow 8 20, 31962656518858185120⟩, ⟨.privateRow 8 21, 101454499624465587600⟩, ⟨.privateRow 8 22, 53259123165692908464⟩, ⟨.privateRow 9 12, 102608849177714880⟩, ⟨.privateRow 9 13, 828763781820004800⟩, ⟨.privateRow 9 14, 2603699547884515080⟩, ⟨.privateRow 9 15, 5664474878469760080⟩, ⟨.privateRow 9 16, 10307058899901459696⟩, ⟨.privateRow 9 17, 16839252248387208640⟩, ⟨.privateRow 9 18, 25520744706419772810⟩, ⟨.privateRow 9 19, 33296571558168478560⟩, ⟨.privateRow 10 10, 76956636883286160⟩, ⟨.privateRow 10 11, 626646900335330160⟩, ⟨.privateRow 10 12, 1882477732991153760⟩, ⟨.privateRow 10 13, 4040223436372523400⟩, ⟨.privateRow 10 14, 7324872619709146320⟩, ⟨.privateRow 10 15, 11935974380597683416⟩, ⟨.privateRow 10 16, 9414361912055340240⟩, ⟨.privateRow 11 8, 72146847078080775⟩, ⟨.privateRow 11 9, 564348670477431840⟩, ⟨.privateRow 11 10, 1676555303528734200⟩, ⟨.privateRow 11 11, 3492647366241448800⟩, ⟨.privateRow 11 12, 6829901523391646700⟩, ⟨.privateRow 12 6, 99590941848958560⟩, ⟨.privateRow 12 7, 634892254287110820⟩, ⟨.privateRow 12 8, 1918785479623268256⟩, ⟨.privateRow 12 9, 1874443798371470040⟩, ⟨.privateRow 13 4, 141087167619357960⟩, ⟨.privateRow 13 5, 896318476640627040⟩, ⟨.privateRow 13 6, 476169190715333115⟩, ⟨.hall 4 29, 362650455648797700384⟩, ⟨.hall 3 30, 1232182502804185012080⟩, ⟨.hall 2 31, 3172821133111979063715⟩, ⟨.assumptionRow 19, 2721608483468160⟩]
  caps := #[0, 432531212062947426000, 0, 4154956191238881600, 3980319088449132000, 322664677307729328, 1647631142368594500, 277709627943427680, 1235832129908579720, 1963265829177734768, 13729518177073710, 3731093136291447630, 0, 0, 111519886005061522560, 38931454415340938880, 11755438655581969920] }

theorem case_50_34_19_checked :
    (Witness.linear .conditional case_50_34_19).check 50 34 19 = true := by
  change case_50_34_19.check 50 34 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_34_20 : Certificate := {
  objectiveScale := 17420337144836545920000
  eta := 2491773160678853943473602020000
  rows := #[⟨.count 2, 323421985753418593479430792800⟩, ⟨.count 3, 40246132099594317337736895600⟩, ⟨.count 4, 4604667154966081294959067200⟩, ⟨.count 5, 465682357905145762030650000⟩, ⟨.count 6, 30481027062882268060188000⟩, ⟨.path 6, 14525537677348740234192000⟩, ⟨.path 7, 1363437823788433961568000⟩, ⟨.privateRow 3 29, 20050419601963955929991666400⟩, ⟨.privateRow 4 24, 1596625227103356898390800⟩, ⟨.privateRow 4 25, 709699913447442141334710600⟩, ⟨.privateRow 4 26, 1573633823833068559053972480⟩, ⟨.privateRow 4 27, 4599078966671219545814699400⟩, ⟨.privateRow 5 22, 86616918570357111737700900⟩, ⟨.privateRow 5 23, 390640972231287987806282400⟩, ⟨.privateRow 5 24, 732673576437429332261556000⟩, ⟨.privateRow 5 25, 1456654415527295943631873200⟩, ⟨.privateRow 5 26, 2451351932012687291329341600⟩, ⟨.privateRow 5 27, 2515926552308867503664258400⟩, ⟨.privateRow 6 19, 8636291001149975950386600⟩, ⟨.privateRow 6 20, 55881882948617491443678000⟩, ⟨.privateRow 6 22, 61445879952159492756252000⟩, ⟨.privateRow 6 25, 6012382588153527374872083000⟩, ⟨.privateRow 7 16, 592686637333821878948100⟩, ⟨.privateRow 7 19, 100474496614685994716916000⟩, ⟨.privateRow 7 21, 124681915461980325065245200⟩, ⟨.privateRow 7 22, 147324964137264295624242000⟩, ⟨.privateRow 7 25, 5112006916523832823338640800⟩, ⟨.privateRow 8 14, 547095357538912503644400⟩, ⟨.privateRow 8 16, 2801791376487157973209200⟩, ⟨.privateRow 8 18, 120556852305087028117887600⟩, ⟨.privateRow 8 24, 1103977643140465553187327600⟩, ⟨.privateRow 8 25, 1226861339281011289422567000⟩, ⟨.privateRow 9 12, 451570771301959526817600⟩, ⟨.privateRow 9 13, 182365119179637501214800⟩, ⟨.privateRow 9 14, 1843913982816334734505200⟩, ⟨.privateRow 9 15, 2442587353860599258695200⟩, ⟨.privateRow 9 17, 263416283259476390643600⟩, ⟨.privateRow 9 18, 11853732746676437578962000⟩, ⟨.privateRow 9 21, 153308276857015259354575200⟩, ⟨.privateRow 9 23, 1246749268667101756916158800⟩, ⟨.privateRow 10 10, 338678078476469645113200⟩, ⟨.privateRow 10 11, 217721621877730486144200⟩, ⟨.privateRow 10 12, 1094190715077825007288800⟩, ⟨.privateRow 10 13, 2032068470858817870679200⟩, ⟨.privateRow 10 14, 1662601476157214621464800⟩, ⟨.privateRow 13 18, 2794094147430874572183900⟩, ⟨.hall 11 5, 1107152920812257748000⟩, ⟨.hall 10 6, 440344911686693422500⟩, ⟨.hall 13 6, 1785012723799762614300⟩, ⟨.hall 10 7, 2813314713553874643750⟩, ⟨.hall 11 7, 1777957337539684501200⟩, ⟨.hall 9 9, 175060414773138166272⟩, ⟨.hall 12 9, 449373832564975203600⟩, ⟨.hall 9 10, 643110792197483781990⟩, ⟨.hall 7 13, 866747166765151672⟩, ⟨.hall 7 15, 197882014873883141340⟩, ⟨.hall 5 20, 737568982347971413200⟩, ⟨.hall 4 25, 354554638308716763250080⟩, ⟨.hall 3 26, 919416173293778329128960⟩, ⟨.hall 2 29, 56821760137636801761238785⟩]
  caps := #[0, 0, 0, 0, 74512748049179789935254240, 0, 4252193251265269954644000, 1662443806592418024096000, 6349056753023438190434600, 16756004579502058112970, 11612639237880706848542520, 60287823324017471432250, 45029873036530849639972800, 12097630899593993048724000, 0, 270084907093545807943680000, 95951216993759694927360000] }

theorem case_50_34_20_checked :
    (Witness.linear .negative case_50_34_20).check 50 34 20 = true := by
  change case_50_34_20.check 50 34 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_34_21 : Certificate := {
  objectiveScale := 102615228710065500000
  eta := 13196126206607983337613915000
  rows := #[⟨.count 2, 1580552969379035292414774000⟩, ⟨.count 3, 173818224125780700621355200⟩, ⟨.count 4, 16516663830956537163115200⟩, ⟨.count 5, 1310846335790201362152000⟩, ⟨.count 6, 89375886531150092874000⟩, ⟨.path 5, 239120406865394013960000⟩, ⟨.path 6, 57887959428842142600000⟩, ⟨.privateRow 8 15, 579288153442639490850⟩, ⟨.hall 13 8, 4187184226564602120⟩, ⟨.hall 11 9, 3569100328116102780⟩, ⟨.hall 12 9, 2964702118459202550⟩, ⟨.hall 10 12, 1707650792869477500⟩, ⟨.hall 8 14, 2723662618586555184⟩, ⟨.hall 9 14, 3500926501623997446⟩, ⟨.hall 7 15, 2169748850195361820⟩, ⟨.hall 6 17, 1102934311380214500⟩, ⟨.hall 10 17, 9425547980916078375⟩]
  caps := #[0, 26137056051489133121085000, 0, 0, 183662303628232173544800, 0, 0, 0, 39507506419763705759150, 0, 0, 64427971844094547313625, 0, 508278021505942204416900, 0, 2386419758881283268000000, 1025741826185814738000000] }

theorem case_50_34_21_checked :
    (Witness.linear .negative case_50_34_21).check 50 34 21 = true := by
  change case_50_34_21.check 50 34 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_34_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58786, 58786, 41990, 25194, 13260] }

theorem case_50_34_22_checked :
    (Witness.linear .negative case_50_34_22).check 50 34 22 = true := by
  change case_50_34_22.check 50 34 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_35_1_checked :
    (Witness.rising).check 50 35 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_35_2_checked :
    (Witness.rising).check 50 35 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_35_3_checked :
    (Witness.rising).check 50 35 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_35_4_checked :
    (Witness.rising).check 50 35 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_35_5_checked :
    (Witness.rising).check 50 35 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_35_6_checked :
    (Witness.rising).check 50 35 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_35_7_checked :
    (Witness.rising).check 50 35 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_35_8_checked :
    (Witness.rising).check 50 35 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_35_9_checked :
    (Witness.rising).check 50 35 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_35_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_50_35_10_checked :
    (Witness.linear .positive case_50_35_10).check 50 35 10 = true := by
  change case_50_35_10.check 50 35 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_35_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_50_35_11_checked :
    (Witness.linear .positive case_50_35_11).check 50 35 11 = true := by
  change case_50_35_11.check 50 35 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_35_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_50_35_12_checked :
    (Witness.linear .positive case_50_35_12).check 50 35 12 = true := by
  change case_50_35_12.check 50 35 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_35_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_50_35_13_checked :
    (Witness.linear .positive case_50_35_13).check 50 35 13 = true := by
  change case_50_35_13.check 50 35 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_35_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_50_35_14_checked :
    (Witness.linear .positive case_50_35_14).check 50 35 14 = true := by
  change case_50_35_14.check 50 35 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_35_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_50_35_15_checked :
    (Witness.linear .positive case_50_35_15).check 50 35 15 = true := by
  change case_50_35_15.check 50 35 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_35_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_50_35_16_checked :
    (Witness.linear .positive case_50_35_16).check 50 35 16 = true := by
  change case_50_35_16.check 50 35 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_35_17 : Certificate := {
  objectiveScale := 614
  eta := 3035981025
  rows := #[⟨.assumptionRow 17, 1215⟩]
  caps := #[0, 0, 864364150, 248485192, 72232490, 21269550, 6358170, 1934920, 601601, 192005, 63300, 17974132, 11196262, 4661041, 1497370, 376750] }

theorem case_50_35_17_checked :
    (Witness.linear .conditional case_50_35_17).check 50 35 17 = true := by
  change case_50_35_17.check 50 35 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_35_18 : Certificate := {
  objectiveScale := 3685876365600000
  eta := 809097356948209564435200
  rows := #[⟨.count 2, 84444627060128668132800⟩, ⟨.count 3, 7963216811956932926400⟩, ⟨.count 4, 668996534337845313600⟩, ⟨.count 5, 49046666740311240000⟩, ⟨.path 5, 29003453598679560000⟩, ⟨.privateRow 2 32, 7153946810741797466400⟩, ⟨.privateRow 2 33, 11221877350183211712000⟩, ⟨.privateRow 3 28, 487720054065654970560⟩, ⟨.privateRow 3 29, 1354178468699993336400⟩, ⟨.privateRow 3 30, 2877404448764926080000⟩, ⟨.privateRow 3 31, 3506836671932253660000⟩, ⟨.privateRow 3 32, 5308811207971288617600⟩, ⟨.privateRow 4 25, 147210066887705593200⟩, ⟨.privateRow 4 26, 266159911510755662400⟩, ⟨.privateRow 4 27, 649574054308682062560⟩, ⟨.privateRow 4 28, 950892251427784165500⟩, ⟨.privateRow 4 29, 1291235246383260578400⟩, ⟨.privateRow 4 30, 1820857502734054785000⟩, ⟨.privateRow 5 20, 178351515419313600⟩, ⟨.privateRow 5 22, 26594192632524316800⟩, ⟨.privateRow 5 23, 59591700089478156600⟩, ⟨.privateRow 5 24, 142375466880446342400⟩, ⟨.privateRow 5 25, 248503111484243616000⟩, ⟨.privateRow 5 26, 362160587210458196160⟩, ⟨.privateRow 5 27, 487033400731290613200⟩, ⟨.privateRow 5 28, 721966934417381452800⟩, ⟨.privateRow 5 29, 583655334209703756000⟩, ⟨.privateRow 6 10, 98093333480622480⟩, ⟨.privateRow 6 19, 3210327277547644800⟩, ⟨.privateRow 6 20, 11869293351155320080⟩, ⟨.privateRow 6 21, 33896696347192879200⟩, ⟨.privateRow 6 22, 64373750096658502500⟩, ⟨.privateRow 6 23, 104399333490091068000⟩, ⟨.privateRow 6 24, 152535133562367956400⟩, ⟨.privateRow 6 25, 130267946862266653440⟩, ⟨.privateRow 6 26, 448286534006444733600⟩, ⟨.privateRow 6 27, 82398400123722883200⟩, ⟨.privateRow 7 10, 34418713501972800⟩, ⟨.privateRow 7 16, 100608547159612800⟩, ⟨.privateRow 7 17, 1689385187721831600⟩, ⟨.privateRow 7 18, 7728565668170256000⟩, ⟨.privateRow 7 19, 18245360027395781280⟩, ⟨.privateRow 7 20, 32116483998840841600⟩, ⟨.privateRow 7 21, 50354577853386206400⟩, ⟨.privateRow 7 22, 72682488998023132800⟩, ⟨.privateRow 7 23, 96894414960303760800⟩, ⟨.privateRow 7 24, 103586560155537338880⟩, ⟨.privateRow 8 15, 1320487181469918000⟩, ⟨.privateRow 8 16, 5197584267063538350⟩, ⟨.privateRow 8 17, 11080087895424857400⟩, ⟨.privateRow 8 18, 18825745583822797620⟩, ⟨.privateRow 8 19, 28801292635838322600⟩, ⟨.privateRow 8 20, 40984620894872579925⟩, ⟨.privateRow 8 21, 32043822270336676800⟩, ⟨.privateRow 9 13, 1074355557168722400⟩, ⟨.privateRow 9 14, 4024341886384512000⟩, ⟨.privateRow 9 15, 8174444456718540000⟩, ⟨.privateRow 9 16, 12484606079351952000⟩, ⟨.privateRow 9 17, 22626862256196918720⟩, ⟨.privateRow 10 11, 1046328890459973120⟩, ⟨.privateRow 10 12, 3713533338909279600⟩, ⟨.privateRow 10 13, 7545641036970960000⟩, ⟨.privateRow 10 14, 4414200006628011600⟩, ⟨.privateRow 11 9, 1226166668507781000⟩, ⟨.privateRow 11 10, 4316106673147389120⟩, ⟨.privateRow 12 7, 1904164708741495200⟩, ⟨.hall 4 30, 24365118316154616000⟩, ⟨.hall 3 31, 576604875865784015250⟩, ⟨.assumptionRow 18, 3204943217416512⟩]
  caps := #[0, 24742979425738379520, 140464170335057231520, 33534441579242260800, 14315703563867371380, 7027774982610528744, 475934952396679776, 0, 6715956302428455345, 190365193829416320, 2628608928202730880, 14230491699528293904, 3204943217416512, 116995610002757758272, 38024917438404536640, 10611475878002313600] }

theorem case_50_35_18_checked :
    (Witness.linear .conditional case_50_35_18).check 50 35 18 = true := by
  change case_50_35_18.check 50 35 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_35_19 : Certificate := {
  objectiveScale := 607085519040000
  eta := 145912460245757210285280
  rows := #[⟨.count 2, 15205643809498251869760⟩, ⟨.count 3, 1411366882119196242240⟩, ⟨.count 4, 110060720165258422560⟩, ⟨.count 5, 5885600008837348800⟩, ⟨.path 5, 5248780340576572800⟩, ⟨.privateRow 2 32, 1360652628709714420080⟩, ⟨.privateRow 2 33, 2216320776661184313120⟩, ⟨.privateRow 3 28, 78984752118597220896⟩, ⟨.privateRow 3 29, 245478567035257756200⟩, ⟨.privateRow 3 30, 545268143040953492160⟩, ⟨.privateRow 3 31, 698130254381590190160⟩, ⟨.privateRow 3 32, 1096291094979436836480⟩, ⟨.privateRow 4 25, 23507366701963458600⟩, ⟨.privateRow 4 26, 44959444511951970000⟩, ⟨.privateRow 4 27, 116858588175465560424⟩, ⟨.privateRow 4 28, 180332331937439351670⟩, ⟨.privateRow 4 29, 257168022608365268400⟩, ⟨.privateRow 4 30, 383054467241830784400⟩, ⟨.privateRow 5 21, 215805333657369456⟩, ⟨.privateRow 5 22, 4119920006186144160⟩, ⟨.privateRow 5 23, 9416960014139758080⟩, ⟨.privateRow 5 24, 23794640035728138720⟩, ⟨.privateRow 5 25, 44240093399760738480⟩, ⟨.privateRow 5 26, 68037536102159752128⟩, ⟨.privateRow 5 27, 97063353479075943960⟩, ⟨.privateRow 5 28, 153941138008923545280⟩, ⟨.privateRow 5 29, 140273466877290146400⟩, ⟨.privateRow 6 18, 32697777826874160⟩, ⟨.privateRow 6 19, 606395152425666240⟩, ⟨.privateRow 6 20, 1775489335999266888⟩, ⟨.privateRow 6 21, 5253442970851115040⟩, ⟨.privateRow 6 22, 10594080015907227840⟩, ⟨.privateRow 6 23, 18259373360750155920⟩, ⟨.privateRow 6 24, 28283577820246148400⟩, ⟨.privateRow 6 25, 40198648060359092304⟩, ⟨.privateRow 6 26, 64422796763398813740⟩, ⟨.privateRow 6 27, 61373728981042798320⟩, ⟨.privateRow 7 16, 70425983011728960⟩, ⟨.privateRow 7 17, 299729630079679800⟩, ⟨.privateRow 7 18, 1135504648169629920⟩, ⟨.privateRow 7 19, 2772771559718928768⟩, ⟨.privateRow 7 20, 5173515069496533760⟩, ⟨.privateRow 7 21, 8599515568467904080⟩, ⟨.privateRow 7 22, 13191217797584661120⟩, ⟨.privateRow 7 23, 18790322991177017280⟩, ⟨.privateRow 7 24, 30304300489946971488⟩, ⟨.privateRow 7 25, 11002802238743154840⟩, ⟨.privateRow 8 13, 3814740746468652⟩, ⟨.privateRow 8 14, 40872222283592700⟩, ⟨.privateRow 8 15, 233286068726352180⟩, ⟨.privateRow 8 16, 748642871494472955⟩, ⟨.privateRow 8 17, 1659412224713863620⟩, ⟨.privateRow 8 18, 2958331448886439626⟩, ⟨.privateRow 8 19, 4787499636818158260⟩, ⟨.privateRow 8 20, 7224165288625009725⟩, ⟨.privateRow 8 21, 10242578904268330620⟩, ⟨.privateRow 8 22, 6961901862305289900⟩, ⟨.privateRow 9 11, 4087222228359270⟩, ⟨.privateRow 9 12, 39237333392248992⟩, ⟨.privateRow 9 13, 196186666961244960⟩, ⟨.privateRow 9 14, 578499146167773600⟩, ⟨.privateRow 9 15, 1198918520318719200⟩, ⟨.privateRow 9 16, 2080767679891992000⟩, ⟨.privateRow 9 17, 3289396449383540496⟩, ⟨.privateRow 9 18, 4875601982629458080⟩, ⟨.privateRow 9 19, 490466667403112400⟩, ⟨.privateRow 10 9, 5770196087095440⟩, ⟨.privateRow 10 10, 49046666740311240⟩, ⟨.privateRow 10 11, 202726222526619792⟩, ⟨.privateRow 10 12, 546520000820610960⟩, ⟨.privateRow 10 13, 1094117950360789200⟩, ⟨.privateRow 10 14, 1871947780588545660⟩, ⟨.privateRow 10 15, 847169698241739600⟩, ⟨.privateRow 11 7, 10899259275624720⟩, ⟨.privateRow 11 8, 69242353045145280⟩, ⟨.privateRow 11 9, 257495000386634010⟩, ⟨.privateRow 11 10, 667034667668232864⟩, ⟨.privateRow 11 11, 630600000946858800⟩, ⟨.privateRow 12 6, 119891852031871920⟩, ⟨.privateRow 12 7, 412569020227323960⟩, ⟨.privateRow 13 4, 113581754556510240⟩, ⟨.hall 4 30, 18587104544037949920⟩, ⟨.hall 3 31, 134945772702623837955⟩, ⟨.assumptionRow 19, 344592581419944⟩]
  caps := #[0, 44310684588009325200, 2814887439783258840, 4418168369968390752, 3855842280559088820, 0, 423549461915429460, 512399863838621256, 313790769014242146, 82356964502311224, 248567802321563028, 0, 1408077864032971560, 14910023367872857224, 15639577538725524384, 5194209033286467480] }

theorem case_50_35_19_checked :
    (Witness.linear .conditional case_50_35_19).check 50 35 19 = true := by
  change case_50_35_19.check 50 35 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_35_20 : Certificate := {
  objectiveScale := 44758957443200000
  eta := 16648029111575134015142400
  rows := #[⟨.count 2, 1785774748992488423769600⟩, ⟨.count 3, 172342139458775247561600⟩, ⟨.count 4, 14559666510750525964800⟩, ⟨.count 5, 863221334629477824000⟩, ⟨.count 6, 43161066731473891200⟩, ⟨.path 5, 478040741676618120000⟩, ⟨.path 6, 24344981854736306400⟩, ⟨.privateRow 2 32, 164587534469353771776000⟩, ⟨.privateRow 3 28, 8704148457513901392000⟩, ⟨.privateRow 3 30, 122174592894558761356800⟩, ⟨.privateRow 3 31, 42017298463089833083200⟩, ⟨.privateRow 4 25, 2707329292953999199200⟩, ⟨.privateRow 4 26, 5209300970784834924000⟩, ⟨.privateRow 4 28, 44124098032919902397400⟩, ⟨.privateRow 4 29, 27338939018827753917600⟩, ⟨.privateRow 4 30, 41087537150582666343600⟩, ⟨.privateRow 5 25, 13670068968674036318400⟩, ⟨.privateRow 5 26, 2221356234446522933760⟩, ⟨.privateRow 5 27, 15879675801621435804000⟩, ⟨.privateRow 5 28, 18309883642307479622400⟩, ⟨.privateRow 5 29, 17847101093464454011200⟩, ⟨.privateRow 6 19, 39891288948786475200⟩, ⟨.privateRow 6 20, 33090151160796649920⟩, ⟨.privateRow 6 21, 230991634914739899200⟩, ⟨.privateRow 6 23, 4252392717496165756800⟩, ⟨.privateRow 6 24, 4058339191278864492000⟩, ⟨.privateRow 6 25, 3061558333485881349120⟩, ⟨.privateRow 6 26, 7380542411082035395200⟩, ⟨.privateRow 6 27, 13413500405325830409600⟩, ⟨.privateRow 7 15, 342548148662491200⟩, ⟨.privateRow 7 16, 6271266106282531200⟩, ⟨.privateRow 7 18, 85014222349872816000⟩, ⟨.privateRow 7 19, 128044497970039210560⟩, ⟨.privateRow 7 21, 1463879513309156143200⟩, ⟨.privateRow 7 22, 2171755262520194208000⟩, ⟨.privateRow 7 23, 2531316635899589137600⟩, ⟨.privateRow 7 24, 2705719316655285490560⟩, ⟨.privateRow 7 25, 4254961828611134440800⟩, ⟨.privateRow 8 12, 262263426319719825⟩, ⟨.privateRow 8 13, 1118990618964137920⟩, ⟨.privateRow 8 16, 7343375936952155100⟩, ⟨.privateRow 8 17, 212481059578303916400⟩, ⟨.privateRow 8 19, 440602556217129306000⟩, ⟨.privateRow 8 21, 3885095465092809567600⟩, ⟨.privateRow 8 22, 1088218376942624127200⟩, ⟨.privateRow 8 25, 415425267290436202800⟩, ⟨.privateRow 9 11, 299729630079679800⟩, ⟨.privateRow 9 14, 2951184050015308800⟩, ⟨.privateRow 9 23, 4013979206027071881600⟩, ⟨.privateRow 10 9, 423147713053665600⟩, ⟨.privateRow 10 12, 2569111114968684000⟩, ⟨.privateRow 10 13, 1106694018755740800⟩, ⟨.privateRow 10 14, 2997296300796798000⟩, ⟨.privateRow 10 22, 307522600461751474800⟩, ⟨.hall 11 4, 3723349441983600⟩, ⟨.hall 13 4, 281250058901834880⟩, ⟨.hall 10 6, 11454376828793184⟩, ⟨.hall 10 7, 5447135528138304⟩, ⟨.hall 11 7, 5944294723166800⟩, ⟨.hall 12 7, 4518739880054400⟩, ⟨.hall 8 9, 1523581253197696⟩, ⟨.hall 9 9, 2672918152226784⟩, ⟨.hall 9 10, 348046797954240⟩, ⟨.hall 6 14, 21888805658720⟩, ⟨.hall 2 29, 12368198154771819360⟩, ⟨.hall 4 29, 146345409060839788800⟩, ⟨.hall 3 30, 670519354232604977100⟩]
  caps := #[0, 3440008064939015388000, 519145367844138890400, 739856060798416598400, 0, 184560190715694743040, 0, 45678479207358011520, 10665068772383872, 8188781584947346240, 48973147963147548800, 97402821402290976, 70962462452917235200, 775516881800838777600, 0, 1040914314299059200000] }

theorem case_50_35_20_checked :
    (Witness.linear .negative case_50_35_20).check 50 35 20 = true := by
  change case_50_35_20.check 50 35 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_35_21 : Certificate := {
  objectiveScale := 60424592548320000
  eta := 21062061051625115481960000
  rows := #[⟨.count 2, 2240447812964078218300800⟩, ⟨.count 3, 210442571115983825018400⟩, ⟨.count 4, 16023546024059682108000⟩, ⟨.count 5, 809270001215135460000⟩, ⟨.path 5, 708543107938615950000⟩, ⟨.path 6, 7154443647106179840⟩, ⟨.privateRow 8 15, 726267949808454900⟩, ⟨.hall 9 9, 155402218152720⟩, ⟨.hall 10 9, 316898640938880⟩, ⟨.hall 12 9, 1742942525163840⟩, ⟨.hall 8 10, 419522037482240⟩, ⟨.hall 11 10, 953171693448975⟩, ⟨.hall 8 12, 1518246943216080⟩, ⟨.hall 7 13, 1305189599283570⟩, ⟨.hall 9 13, 1669801187054286⟩, ⟨.hall 10 13, 1612221835776552⟩, ⟨.hall 11 14, 1134728206486875⟩, ⟨.hall 6 16, 1077215435868000⟩, ⟨.hall 5 21, 2803061721213600⟩]
  caps := #[0, 11537878949748859584240, 0, 230675356275221613600, 77015930231121008400, 19931855243512427280, 7154443647106179840, 31038520180086619200, 15874142331527657100, 9750050279655840, 37196275261920390000, 0, 0, 0, 5269628716138987200000, 2342057207172883200000] }

theorem case_50_35_21_checked :
    (Witness.linear .negative case_50_35_21).check 50 35 21 = true := by
  change case_50_35_21.check 50 35 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_35_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208012, 208012, 149226, 90440, 48450] }

theorem case_50_35_22_checked :
    (Witness.linear .negative case_50_35_22).check 50 35 22 = true := by
  change case_50_35_22.check 50 35 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_36_1_checked :
    (Witness.rising).check 50 36 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_36_2_checked :
    (Witness.rising).check 50 36 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_36_3_checked :
    (Witness.rising).check 50 36 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_36_4_checked :
    (Witness.rising).check 50 36 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_36_5_checked :
    (Witness.rising).check 50 36 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_36_6_checked :
    (Witness.rising).check 50 36 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_36_7_checked :
    (Witness.rising).check 50 36 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_36_8_checked :
    (Witness.rising).check 50 36 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_36_9_checked :
    (Witness.rising).check 50 36 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_36_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_50_36_10_checked :
    (Witness.linear .positive case_50_36_10).check 50 36 10 = true := by
  change case_50_36_10.check 50 36 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_36_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_50_36_11_checked :
    (Witness.linear .positive case_50_36_11).check 50 36 11 = true := by
  change case_50_36_11.check 50 36 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_36_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_50_36_12_checked :
    (Witness.linear .positive case_50_36_12).check 50 36 12 = true := by
  change case_50_36_12.check 50 36 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_36_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_50_36_13_checked :
    (Witness.linear .positive case_50_36_13).check 50 36 13 = true := by
  change case_50_36_13.check 50 36 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_36_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_50_36_14_checked :
    (Witness.linear .positive case_50_36_14).check 50 36 14 = true := by
  change case_50_36_14.check 50 36 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_36_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_50_36_15_checked :
    (Witness.linear .positive case_50_36_15).check 50 36 15 = true := by
  change case_50_36_15.check 50 36 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_36_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_50_36_16_checked :
    (Witness.linear .positive case_50_36_16).check 50 36 16 = true := by
  change case_50_36_16.check 50 36 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_36_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_50_36_17_checked :
    (Witness.linear .positive case_50_36_17).check 50 36 17 = true := by
  change case_50_36_17.check 50 36 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_36_18 : Certificate := {
  objectiveScale := 960
  eta := 6690583620
  rows := #[⟨.assumptionRow 18, 1459⟩]
  caps := #[0, 0, 1923217335, 557472160, 163111124, 48230360, 14751410, 4682106, 1512888, 499499, 180154975, 133887600, 68685452, 28431634, 9832515] }

theorem case_50_36_18_checked :
    (Witness.linear .conditional case_50_36_18).check 50 36 18 = true := by
  change case_50_36_18.check 50 36 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_36_19 : Certificate := {
  objectiveScale := 29209971831040000
  eta := 17735294707340168331172800
  rows := #[⟨.count 2, 1461965154060679194326400⟩, ⟨.count 3, 103896000796190399596800⟩, ⟨.count 4, 5397194846555345433600⟩, ⟨.count 5, 112441559303236363200⟩, ⟨.path 4, 3331583350493387109120⟩, ⟨.path 5, 83586263749825636800⟩, ⟨.privateRow 2 33, 121212000928888799529600⟩, ⟨.privateRow 2 34, 181818001393333199294400⟩, ⟨.privateRow 3 29, 12286114379866959952320⟩, ⟨.privateRow 3 30, 23139535891611849910200⟩, ⟨.privateRow 3 31, 48924571803497066476800⟩, ⟨.privateRow 3 32, 56792357578076299779600⟩, ⟨.privateRow 3 33, 81426429195426999684000⟩, ⟨.privateRow 4 25, 660594160906513633800⟩, ⟨.privateRow 4 26, 2955606701685070118400⟩, ⟨.privateRow 4 27, 4928688349458527253600⟩, ⟨.privateRow 4 28, 11300376709975254501600⟩, ⟨.privateRow 4 29, 16261860514230559027800⟩, ⟨.privateRow 4 30, 21570039126337509007200⟩, ⟨.privateRow 4 31, 29375357367970499886000⟩, ⟨.privateRow 5 21, 4088783974663140480⟩, ⟨.privateRow 5 22, 211390131490084362816⟩, ⟨.privateRow 5 23, 589693511012528482560⟩, ⟨.privateRow 5 24, 1141281826927849086480⟩, ⟨.privateRow 5 25, 2634345103675823366400⟩, ⟨.privateRow 5 26, 4430197436547512710080⟩, ⟨.privateRow 5 27, 6373187581307437066176⟩, ⟨.privateRow 5 28, 8455605259603374512640⟩, ⟨.privateRow 5 29, 12308602691727607224960⟩, ⟨.privateRow 5 30, 6195529917608323612320⟩, ⟨.privateRow 6 19, 48932900807889898800⟩, ⟨.privateRow 6 20, 134021252502847382400⟩, ⟨.privateRow 6 21, 263612989033143029280⟩, ⟨.privateRow 6 22, 673261188420612792000⟩, ⟨.privateRow 6 23, 1235295464011943934600⟩, ⟨.privateRow 6 24, 1952556601233977481600⟩, ⟨.privateRow 6 25, 2817285735875533322400⟩, ⟨.privateRow 6 26, 3728062366231747864320⟩, ⟨.privateRow 6 27, 5506513029211269675600⟩, ⟨.privateRow 7 16, 10708719933641558400⟩, ⟨.privateRow 7 17, 35318182088837062800⟩, ⟨.privateRow 7 18, 71837662888178787600⟩, ⟨.privateRow 7 19, 183995278859841321600⟩, ⟨.privateRow 7 20, 387923379596165453040⟩, ⟨.privateRow 7 21, 660073598131961613600⟩, ⟨.privateRow 7 22, 1011974033729127268800⟩, ⟨.privateRow 7 23, 1441661421066494799600⟩, ⟨.privateRow 7 24, 1914629884802330295600⟩, ⟨.privateRow 7 25, 569703900469730906880⟩, ⟨.privateRow 8 13, 2928165606855113625⟩, ⟨.privateRow 8 14, 10619480600861212080⟩, ⟨.privateRow 8 15, 24763914846546103800⟩, ⟨.privateRow 8 16, 63428571914646153600⟩, ⟨.privateRow 8 17, 126496754216140908600⟩, ⟨.privateRow 8 18, 284511218236976858400⟩, ⟨.privateRow 8 19, 419781821398749089280⟩, ⟨.privateRow 8 20, 642374463797192926800⟩, ⟨.privateRow 8 21, 733212667956520451700⟩, ⟨.privateRow 9 10, 694083699402693600⟩, ⟨.privateRow 9 11, 3674560761543672000⟩, ⟨.privateRow 9 12, 10931818265592424200⟩, ⟨.privateRow 9 13, 29151515374913131200⟩, ⟨.privateRow 9 14, 63359926274045887200⟩, ⟨.privateRow 9 15, 118207793113658740800⟩, ⟨.privateRow 9 16, 237376625195721211200⟩, ⟨.privateRow 9 17, 364583237740796692800⟩, ⟨.privateRow 9 18, 1249350658924848480⟩, ⟨.privateRow 10 8, 2367190722173397120⟩, ⟨.privateRow 10 9, 4997402635699393920⟩, ⟨.privateRow 10 10, 17196944364024384960⟩, ⟨.privateRow 10 11, 25299350843228181720⟩, ⟨.privateRow 10 12, 112441559303236363200⟩, ⟨.privateRow 10 13, 128504639203698700800⟩, ⟨.privateRow 11 6, 2811038982580909080⟩, ⟨.privateRow 11 7, 11835953610866985600⟩, ⟨.privateRow 11 8, 34357143120433333200⟩, ⟨.privateRow 11 9, 49606570280839572000⟩, ⟨.privateRow 12 4, 19632653211676190400⟩, ⟨.privateRow 12 5, 10307142936129999960⟩, ⟨.hall 3 32, 6277987061097363612000⟩, ⟨.assumptionRow 19, 19445148917210016⟩]
  caps := #[0, 9828161429795771462400, 3179294567787771713280, 376206256956686785200, 31086292625638707600, 72055468521103805608, 12194132817320410528, 2139077204110932943, 62237661115556400075, 4341638773734211664, 0, 68469989982095702000, 168789388367563738632, 2903750405923878743232, 1040400942774362865696] }

theorem case_50_36_19_checked :
    (Witness.linear .conditional case_50_36_19).check 50 36 19 = true := by
  change case_50_36_19.check 50 36 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_36_20 : Certificate := {
  objectiveScale := 15900589504800000
  eta := 13854861534745945946232000
  rows := #[⟨.count 2, 1157698294586121595507200⟩, ⟨.count 3, 83694000641375599675200⟩, ⟨.count 4, 4422701332593963619200⟩, ⟨.count 5, 112441559303236363200⟩, ⟨.path 4, 2339143362978388686720⟩, ⟨.path 5, 105860832680447644800⟩, ⟨.privateRow 2 33, 97299429317067199622400⟩, ⟨.privateRow 2 34, 148422858280271999424000⟩, ⟨.privateRow 3 29, 9633742930969506629280⟩, ⟨.privateRow 3 30, 18243642996950099929200⟩, ⟨.privateRow 3 31, 39190047919374288736800⟩, ⟨.privateRow 3 32, 46382143212584999820000⟩, ⟨.privateRow 3 33, 67752286233494533070400⟩, ⟨.privateRow 4 25, 597345783798443179500⟩, ⟨.privateRow 4 26, 2307729145699755835200⟩, ⟨.privateRow 4 27, 3819889639662724227600⟩, ⟨.privateRow 4 28, 8849150717164701783840⟩, ⟨.privateRow 4 29, 12958889709697990858800⟩, ⟨.privateRow 4 30, 17565870264483369628800⟩, ⟨.privateRow 4 31, 24605961227524890813600⟩, ⟨.privateRow 5 21, 24532703847978842880⟩, ⟨.privateRow 5 22, 191150650815501817440⟩, ⟨.privateRow 5 23, 473920349952159190080⟩, ⟨.privateRow 5 24, 881729227536211814760⟩, ⟨.privateRow 5 25, 2022877195464890381760⟩, ⟨.privateRow 5 26, 3433215610725483623040⟩, ⟨.privateRow 5 27, 5025388090459310525952⟩, ⟨.privateRow 5 28, 6843942909590319973440⟩, ⟨.privateRow 5 29, 10337127351944196323520⟩, ⟨.privateRow 5 30, 6446649400052218156800⟩, ⟨.privateRow 6 17, 297464442601154400⟩, ⟨.privateRow 6 18, 9930736006838539200⟩, ⟨.privateRow 6 19, 51709235605500673200⟩, ⟨.privateRow 6 20, 114713105955826996800⟩, ⟨.privateRow 6 21, 209890910699374544640⟩, ⟨.privateRow 6 22, 515472827423067113600⟩, ⟨.privateRow 6 23, 937533556968188380200⟩, ⟨.privateRow 6 24, 1494461359628199705600⟩, ⟨.privateRow 6 25, 2196080824910122550400⟩, ⟨.privateRow 6 26, 2987613875708954331840⟩, ⟨.privateRow 6 27, 4605939429236274729600⟩, ⟨.privateRow 6 28, 1079994236270591241600⟩, ⟨.privateRow 7 14, 195211040457007575⟩, ⟨.privateRow 7 15, 3748051976774545440⟩, ⟨.privateRow 7 16, 15616883236560606000⟩, ⟨.privateRow 7 17, 35318182088837062800⟩, ⟨.privateRow 7 18, 62467532946242424000⟩, ⟨.privateRow 7 19, 145946872428948208800⟩, ⟨.privateRow 7 20, 294222080176801817040⟩, ⟨.privateRow 7 21, 496269845072925924000⟩, ⟨.privateRow 7 22, 765227278591469694000⟩, ⟨.privateRow 7 23, 1109244906459704757600⟩, ⟨.privateRow 7 24, 1511193734524514640600⟩, ⟨.privateRow 7 25, 1108798709795803026000⟩, ⟨.privateRow 8 11, 173520924850673400⟩, ⟨.privateRow 8 12, 1653552342694652400⟩, ⟨.privateRow 8 13, 6051542254167234825⟩, ⟨.privateRow 8 14, 14159307467814949440⟩, ⟨.privateRow 8 15, 25433209842398701200⟩, ⟨.privateRow 8 16, 55019480941113519600⟩, ⟨.privateRow 8 17, 108537338494096211700⟩, ⟨.privateRow 8 18, 199896105427975756800⟩, ⟨.privateRow 8 19, 321707794673148483600⟩, ⟨.privateRow 8 20, 302620492939574409600⟩, ⟨.privateRow 8 21, 1040865267716764389900⟩, ⟨.privateRow 9 9, 1095921630635832000⟩, ⟨.privateRow 9 10, 3007696030745005600⟩, ⟨.privateRow 9 11, 7349121523087344000⟩, ⟨.privateRow 9 12, 14055194912904545400⟩, ⟨.privateRow 9 13, 29706782334435286080⟩, ⟨.privateRow 9 14, 55328386323814718400⟩, ⟨.privateRow 9 15, 100909091682391608000⟩, ⟨.privateRow 9 16, 62120491096541077200⟩, ⟨.privateRow 9 17, 490275485850811752000⟩, ⟨.privateRow 10 7, 3748051976774545440⟩, ⟨.privateRow 10 8, 4339849657317894720⟩, ⟨.privateRow 10 9, 10411255491040404000⟩, ⟨.privateRow 10 10, 22488311860647272640⟩, ⟨.privateRow 10 11, 2342532485484090900⟩, ⟨.privateRow 10 12, 151421299861691635776⟩, ⟨.privateRow 10 13, 78709091512265454240⟩, ⟨.privateRow 11 4, 851829994721487600⟩, ⟨.privateRow 11 5, 8923933278034632000⟩, ⟨.privateRow 11 7, 30576213494739712800⟩, ⟨.privateRow 11 8, 56220779651618181600⟩, ⟨.privateRow 12 2, 5975155325292753600⟩, ⟨.privateRow 12 3, 24987013178496969600⟩, ⟨.privateRow 13 0, 17178571560216666600⟩, ⟨.hall 3 32, 5659558484929563614400⟩, ⟨.assumptionRow 20, 3049521059160576⟩]
  caps := #[0, 2503838782473692664000, 517449521438231141760, 0, 49395206433055874820, 0, 423679195508694840, 23781315074236828650, 1971815386437366855, 13275976306589641280, 0, 0, 827719989485169388608, 0, 1378131624569755351296] }

theorem case_50_36_20_checked :
    (Witness.linear .conditional case_50_36_20).check 50 36 20 = true := by
  change case_50_36_20.check 50 36 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_36_21 : Certificate := {
  objectiveScale := 12616123985214750000
  eta := 16185389267427001380437679000
  rows := #[⟨.count 2, 1155398255639924186016126000⟩, ⟨.count 3, 66405958633891452367291500⟩, ⟨.count 4, 2498029791870524853942000⟩, ⟨.count 5, 59476899806441067951000⟩, ⟨.path 3, 14643744487219995818170500⟩, ⟨.path 4, 1775226635088344442704700⟩, ⟨.path 5, 37144259448312026010000⟩, ⟨.privateRow 6 18, 1016699141990445606000⟩, ⟨.privateRow 6 19, 2202848140979298813000⟩, ⟨.privateRow 7 16, 354029165514530166375⟩, ⟨.privateRow 7 17, 1525048712985668409000⟩, ⟨.hall 11 9, 747230759896060440⟩, ⟨.hall 8 10, 343442011569181800⟩, ⟨.hall 9 10, 81781499529083760⟩, ⟨.hall 10 10, 543067310513870100⟩, ⟨.hall 7 11, 273626630463210750⟩, ⟨.hall 9 11, 17335023733852440⟩, ⟨.hall 8 12, 278707211159557400⟩, ⟨.hall 6 13, 182637418999929465⟩, ⟨.hall 7 13, 215817000497777250⟩, ⟨.hall 12 13, 524205252478103625⟩, ⟨.hall 6 14, 150782196760635440⟩, ⟨.hall 9 14, 312532230527955438⟩, ⟨.hall 5 16, 261359912310697200⟩, ⟨.hall 4 21, 1177880154102680490⟩, ⟨.hall 3 26, 91231097527845185625⟩]
  caps := #[0, 0, 0, 0, 8096714398106096462700, 0, 17376809528965734309000, 5491990900930532068125, 3465620827107445406400, 0, 40293253426322124228000, 49027177813124363391000, 0, 27004838622600142804500, 1882653717817656283500000] }

theorem case_50_36_21_checked :
    (Witness.linear .negative case_50_36_21).check 50 36 21 = true := by
  change case_50_36_21.check 50 36 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_36_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 742900, 742900, 534888, 326876, 177650] }

theorem case_50_36_22_checked :
    (Witness.linear .negative case_50_36_22).check 50 36 22 = true := by
  change case_50_36_22.check 50 36 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_36_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208012, 208012, 149226] }

theorem case_50_36_23_checked :
    (Witness.linear .negative case_50_36_23).check 50 36 23 = true := by
  change case_50_36_23.check 50 36 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_37_1_checked :
    (Witness.rising).check 50 37 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_37_2_checked :
    (Witness.rising).check 50 37 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_37_3_checked :
    (Witness.rising).check 50 37 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_37_4_checked :
    (Witness.rising).check 50 37 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_37_5_checked :
    (Witness.rising).check 50 37 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_37_6_checked :
    (Witness.rising).check 50 37 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_37_7_checked :
    (Witness.rising).check 50 37 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_37_8_checked :
    (Witness.rising).check 50 37 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_37_9_checked :
    (Witness.rising).check 50 37 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_37_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_50_37_10_checked :
    (Witness.linear .positive case_50_37_10).check 50 37 10 = true := by
  change case_50_37_10.check 50 37 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_37_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_50_37_11_checked :
    (Witness.linear .positive case_50_37_11).check 50 37 11 = true := by
  change case_50_37_11.check 50 37 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_37_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_50_37_12_checked :
    (Witness.linear .positive case_50_37_12).check 50 37 12 = true := by
  change case_50_37_12.check 50 37 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_37_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_50_37_13_checked :
    (Witness.linear .positive case_50_37_13).check 50 37 13 = true := by
  change case_50_37_13.check 50 37 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_37_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_50_37_14_checked :
    (Witness.linear .positive case_50_37_14).check 50 37 14 = true := by
  change case_50_37_14.check 50 37 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_37_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_50_37_15_checked :
    (Witness.linear .positive case_50_37_15).check 50 37 15 = true := by
  change case_50_37_15.check 50 37 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_37_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_50_37_16_checked :
    (Witness.linear .positive case_50_37_16).check 50 37 16 = true := by
  change case_50_37_16.check 50 37 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_37_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_50_37_17_checked :
    (Witness.linear .positive case_50_37_17).check 50 37 17 = true := by
  change case_50_37_17.check 50 37 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_37_18 : Certificate := {
  objectiveScale := 883
  eta := 12584289000
  rows := #[⟨.assumptionRow 18, 1635⟩]
  caps := #[0, 0, 3577653450, 1026130625, 297278864, 87119560, 25872300, 7803510, 2397200, 752752, 246675, 99574475, 65387850, 29196706] }

theorem case_50_37_18_checked :
    (Witness.linear .conditional case_50_37_18).check 50 37 18 = true := by
  change case_50_37_18.check 50 37 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_37_19 : Certificate := {
  objectiveScale := 705
  eta := 9887741400
  rows := #[⟨.assumptionRow 19, 947⟩]
  caps := #[0, 0, 2926132335, 871493805, 261463655, 79103992, 24163630, 7463238, 2334644, 753480, 307357050, 244866050, 136107675, 61902016] }

theorem case_50_37_19_checked :
    (Witness.linear .conditional case_50_37_19).check 50 37 19 = true := by
  change case_50_37_19.check 50 37 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_37_20 : Certificate := {
  objectiveScale := 123788464800000
  eta := 251088873511594793875200
  rows := #[⟨.count 2, 16186546877319790171200⟩, ⟨.count 3, 798341395928594918400⟩, ⟨.count 4, 21008984103384076800⟩, ⟨.path 3, 292275967934810059200⟩, ⟨.path 4, 21438160688366401980⟩, ⟨.privateRow 2 34, 1254192582255147334800⟩, ⟨.privateRow 2 35, 1757313982814313924000⟩, ⟨.privateRow 3 29, 43622821159109992800⟩, ⟨.privateRow 3 30, 136558396671996499200⟩, ⟨.privateRow 3 31, 245542501708301397600⟩, ⟨.privateRow 3 32, 510051447398824531200⟩, ⟨.privateRow 3 33, 546233586687985996800⟩, ⟨.privateRow 3 34, 709053213489212592000⟩, ⟨.privateRow 4 25, 4026721953148614720⟩, ⟨.privateRow 4 26, 18350034552799529580⟩, ⟨.privateRow 4 27, 34514759598416697600⟩, ⟨.privateRow 4 28, 54929739686972950800⟩, ⟨.privateRow 4 29, 123532826527898371584⟩, ⟨.privateRow 4 30, 171026261216611000200⟩, ⟨.privateRow 4 31, 216392536264855991040⟩, ⟨.privateRow 4 32, 272328956440116095520⟩, ⟨.privateRow 5 20, 26934595004338560⟩, ⟨.privateRow 5 21, 116716578352133760⟩, ⟨.privateRow 5 22, 1740138077249994240⟩, ⟨.privateRow 5 23, 5205559394505165696⟩, ⟨.privateRow 5 24, 8662963815469483520⟩, ⟨.privateRow 5 25, 13874683251609900720⟩, ⟨.privateRow 5 26, 30796502888055864960⟩, ⟨.privateRow 5 27, 50149223165300138880⟩, ⟨.privateRow 5 28, 69516394066530867456⟩, ⟨.privateRow 5 29, 88675420403033624160⟩, ⟨.privateRow 5 30, 116405334143194736640⟩, ⟨.privateRow 6 17, 9726381529344480⟩, ⟨.privateRow 6 18, 62526738402928800⟩, ⟨.privateRow 6 19, 678976249067701200⟩, ⟨.privateRow 6 20, 1623089917709360100⟩, ⟨.privateRow 6 21, 2699070874393093200⟩, ⟨.privateRow 6 22, 4070490670030664880⟩, ⟨.privateRow 6 23, 8818585919938995200⟩, ⟨.privateRow 6 24, 15391998770187639600⟩, ⟨.privateRow 6 25, 23447526901098300000⟩, ⟨.privateRow 6 26, 32717115869332494600⟩, ⟨.privateRow 6 27, 41901251628416019840⟩, ⟨.privateRow 6 28, 20790140518973826000⟩, ⟨.privateRow 7 14, 7356086870932800⟩, ⟨.privateRow 7 15, 35171290351647450⟩, ⟨.privateRow 7 16, 300128344334058240⟩, ⟨.privateRow 7 17, 660996948830961600⟩, ⟨.privateRow 7 18, 1106242294821048000⟩, ⟨.privateRow 7 19, 1630905760009726200⟩, ⟨.privateRow 7 20, 2432858548768502400⟩, ⟨.privateRow 7 21, 7053016091850368640⟩, ⟨.privateRow 7 22, 8343845869101943200⟩, ⟨.privateRow 7 23, 13341642806724932700⟩, ⟨.privateRow 7 24, 18400725872861904000⟩, ⟨.privateRow 7 25, 3730762058041418400⟩, ⟨.privateRow 8 11, 3839361130004400⟩, ⟨.privateRow 8 12, 24315953823361200⟩, ⟨.privateRow 8 13, 163059925639010400⟩, ⟨.privateRow 8 14, 369298548692298225⟩, ⟨.privateRow 8 15, 627351608642718960⟩, ⟨.privateRow 8 16, 927479952976777200⟩, ⟨.privateRow 8 17, 1655355317974974000⟩, ⟨.privateRow 8 18, 2097251017264903500⟩, ⟨.privateRow 8 19, 5285404144696057200⟩, ⟨.privateRow 8 20, 6908162481216916920⟩, ⟨.privateRow 8 21, 2861177233215501200⟩, ⟨.privateRow 9 8, 5557932302482560⟩, ⟨.privateRow 9 9, 23343315670426752⟩, ⟨.privateRow 9 10, 110573600544126720⟩, ⟨.privateRow 9 11, 278822937174541760⟩, ⟨.privateRow 9 12, 494329037726684160⟩, ⟨.privateRow 9 13, 393918451938451440⟩, ⟨.privateRow 9 15, 5677427846985935040⟩, ⟨.privateRow 9 16, 430953520069416960⟩, ⟨.privateRow 10 5, 11417926143143520⟩, ⟨.privateRow 10 6, 23873845572027360⟩, ⟨.privateRow 10 7, 100042781444686080⟩, ⟨.privateRow 10 8, 275742916356916008⟩, ⟨.privateRow 10 10, 1955002687398240480⟩, ⟨.privateRow 10 11, 247164518863342080⟩, ⟨.privateRow 11 3, 36473930735041800⟩, ⟨.privateRow 11 5, 676425624540775200⟩, ⟨.privateRow 11 6, 166737969074476800⟩, ⟨.privateRow 12 0, 370350681309655200⟩, ⟨.hall 3 33, 23248912555583114400⟩, ⟨.assumptionRow 20, 46779660847920⟩]
  caps := #[0, 7702112363274829500, 0, 5301512506883512920, 480022629291379020, 20647265059362368, 206307062429891500, 0, 1407929175700462835, 21212408819277312, 0, 13879599694886016000, 0, 38304870667159736640] }

theorem case_50_37_20_checked :
    (Witness.linear .conditional case_50_37_20).check 50 37 20 = true := by
  change case_50_37_20.check 50 37 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_37_21 : Certificate := {
  objectiveScale := 51
  eta := 201600750
  rows := #[⟨.assumptionRow 21, 40⟩]
  caps := #[0, 0, 71925945, 24174150, 7811375, 3023603, 1076559, 364344, 139536, 137655, 37579815, 35648275, 24059035, 13599003] }

theorem case_50_37_21_checked :
    (Witness.linear .conditional case_50_37_21).check 50 37 21 = true := by
  change case_50_37_21.check 50 37 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_37_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 2674440, 2674440, 1931540, 1188640, 653752] }

theorem case_50_37_22_checked :
    (Witness.linear .negative case_50_37_22).check 50 37 22 = true := by
  change case_50_37_22.check 50 37 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_37_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 742900, 742900, 534888] }

theorem case_50_37_23_checked :
    (Witness.linear .negative case_50_37_23).check 50 37 23 = true := by
  change case_50_37_23.check 50 37 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_37_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208012] }

theorem case_50_37_24_checked :
    (Witness.linear .negative case_50_37_24).check 50 37 24 = true := by
  change case_50_37_24.check 50 37 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_38_1_checked :
    (Witness.rising).check 50 38 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_38_2_checked :
    (Witness.rising).check 50 38 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_38_3_checked :
    (Witness.rising).check 50 38 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_38_4_checked :
    (Witness.rising).check 50 38 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_38_5_checked :
    (Witness.rising).check 50 38 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_38_6_checked :
    (Witness.rising).check 50 38 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_38_7_checked :
    (Witness.rising).check 50 38 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_38_8_checked :
    (Witness.rising).check 50 38 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_38_9_checked :
    (Witness.rising).check 50 38 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_38_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_50_38_10_checked :
    (Witness.linear .positive case_50_38_10).check 50 38 10 = true := by
  change case_50_38_10.check 50 38 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_38_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_50_38_11_checked :
    (Witness.linear .positive case_50_38_11).check 50 38 11 = true := by
  change case_50_38_11.check 50 38 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_38_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_50_38_12_checked :
    (Witness.linear .positive case_50_38_12).check 50 38 12 = true := by
  change case_50_38_12.check 50 38 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_38_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_50_38_13_checked :
    (Witness.linear .positive case_50_38_13).check 50 38 13 = true := by
  change case_50_38_13.check 50 38 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_38_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_50_38_14_checked :
    (Witness.linear .positive case_50_38_14).check 50 38 14 = true := by
  change case_50_38_14.check 50 38 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_38_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_50_38_15_checked :
    (Witness.linear .positive case_50_38_15).check 50 38 15 = true := by
  change case_50_38_15.check 50 38 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_38_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_50_38_16_checked :
    (Witness.linear .positive case_50_38_16).check 50 38 16 = true := by
  change case_50_38_16.check 50 38 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_38_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_50_38_17_checked :
    (Witness.linear .positive case_50_38_17).check 50 38 17 = true := by
  change case_50_38_17.check 50 38 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_38_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_50_38_18_checked :
    (Witness.linear .positive case_50_38_18).check 50 38 18 = true := by
  change case_50_38_18.check 50 38 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_38_19 : Certificate := {
  objectiveScale := 669
  eta := 13764678900
  rows := #[⟨.assumptionRow 19, 973⟩]
  caps := #[0, 0, 3964051035, 1150146855, 336496555, 99370304, 29654630, 8955498, 2741284, 910455, 462416955, 354175965, 189068165] }

theorem case_50_38_19_checked :
    (Witness.linear .conditional case_50_38_19).check 50 38 19 = true := by
  change case_50_38_19.check 50 38 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_38_20 : Certificate := {
  objectiveScale := 365
  eta := 4211904900
  rows := #[⟨.assumptionRow 20, 381⟩]
  caps := #[0, 0, 1273726545, 384660510, 121573400, 40287467, 13217160, 4312050, 1403520, 763871745, 679764540, 428721150, 225625400] }

theorem case_50_38_20_checked :
    (Witness.linear .conditional case_50_38_20).check 50 38 20 = true := by
  change case_50_38_20.check 50 38 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_38_21 : Certificate := {
  objectiveScale := 398
  eta := 1283091225
  rows := #[⟨.assumptionRow 21, 307⟩]
  caps := #[0, 0, 486182970, 169317720, 56001550, 20646065, 7631844, 2643432, 969000, 1044572025, 997356360, 680356560, 390881205] }

theorem case_50_38_21_checked :
    (Witness.linear .conditional case_50_38_21).check 50 38 21 = true := by
  change case_50_38_21.check 50 38 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_38_22 : Certificate := {
  objectiveScale := 45
  eta := 508300
  rows := #[⟨.assumptionRow 22, 17⟩]
  caps := #[0, 0, 285890, 131054, 63448, 34713, 14478, 8313, 4420, 164812365, 163809450, 117341055, 71466980] }

theorem case_50_38_22_checked :
    (Witness.linear .conditional case_50_38_22).check 50 38 22 = true := by
  change case_50_38_22.check 50 38 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_38_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2674440, 2674440, 1931540] }

theorem case_50_38_23_checked :
    (Witness.linear .negative case_50_38_23).check 50 38 23 = true := by
  change case_50_38_23.check 50 38 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_38_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 742900] }

theorem case_50_38_24_checked :
    (Witness.linear .negative case_50_38_24).check 50 38 24 = true := by
  change case_50_38_24.check 50 38 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_39_1_checked :
    (Witness.rising).check 50 39 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_39_2_checked :
    (Witness.rising).check 50 39 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_39_3_checked :
    (Witness.rising).check 50 39 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_39_4_checked :
    (Witness.rising).check 50 39 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_39_5_checked :
    (Witness.rising).check 50 39 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_39_6_checked :
    (Witness.rising).check 50 39 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_39_7_checked :
    (Witness.rising).check 50 39 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_39_8_checked :
    (Witness.rising).check 50 39 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_39_9_checked :
    (Witness.rising).check 50 39 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_39_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_50_39_10_checked :
    (Witness.linear .positive case_50_39_10).check 50 39 10 = true := by
  change case_50_39_10.check 50 39 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_39_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_50_39_11_checked :
    (Witness.linear .positive case_50_39_11).check 50 39 11 = true := by
  change case_50_39_11.check 50 39 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_39_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_50_39_12_checked :
    (Witness.linear .positive case_50_39_12).check 50 39 12 = true := by
  change case_50_39_12.check 50 39 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_39_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_50_39_13_checked :
    (Witness.linear .positive case_50_39_13).check 50 39 13 = true := by
  change case_50_39_13.check 50 39 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_39_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_50_39_14_checked :
    (Witness.linear .positive case_50_39_14).check 50 39 14 = true := by
  change case_50_39_14.check 50 39 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_39_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_50_39_15_checked :
    (Witness.linear .positive case_50_39_15).check 50 39 15 = true := by
  change case_50_39_15.check 50 39 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_39_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_50_39_16_checked :
    (Witness.linear .positive case_50_39_16).check 50 39 16 = true := by
  change case_50_39_16.check 50 39 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_39_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_50_39_17_checked :
    (Witness.linear .positive case_50_39_17).check 50 39 17 = true := by
  change case_50_39_17.check 50 39 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_39_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_50_39_18_checked :
    (Witness.linear .positive case_50_39_18).check 50 39 18 = true := by
  change case_50_39_18.check 50 39 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_39_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_50_39_19_checked :
    (Witness.linear .positive case_50_39_19).check 50 39 19 = true := by
  change case_50_39_19.check 50 39 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_39_20 : Certificate := {
  objectiveScale := 735
  eta := 15842717400
  rows := #[⟨.assumptionRow 20, 848⟩]
  caps := #[0, 0, 4788643125, 1449507150, 439851425, 133937441, 40966090, 12597000, 4342170, 2575677195, 2214226560, 1347536190] }

theorem case_50_39_20_checked :
    (Witness.linear .conditional case_50_39_20).check 50 39 20 = true := by
  change case_50_39_20.check 50 39 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_39_21 : Certificate := {
  objectiveScale := 535
  eta := 7074015240
  rows := #[⟨.assumptionRow 21, 484⟩]
  caps := #[0, 0, 2271585225, 716245530, 222780415, 78930940, 27048989, 9031080, 3101550, 2374536675, 2204211555, 1459176810] }

theorem case_50_39_21_checked :
    (Witness.linear .conditional case_50_39_21).check 50 39 21 = true := by
  change case_50_39_21.check 50 39 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_39_22 : Certificate := {
  objectiveScale := 77
  eta := 12876435
  rows := #[⟨.assumptionRow 22, 39⟩]
  caps := #[0, 0, 6364215, 2351635, 1157728, 442244, 216657, 86241, 424292040, 678639150, 554887305, 363271545] }

theorem case_50_39_22_checked :
    (Witness.linear .conditional case_50_39_22).check 50 39 22 = true := by
  change case_50_39_22.check 50 39 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_39_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 9694845, 9694845, 7020405] }

theorem case_50_39_23_checked :
    (Witness.linear .negative case_50_39_23).check 50 39 23 = true := by
  change case_50_39_23.check 50 39 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_39_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2674440] }

theorem case_50_39_24_checked :
    (Witness.linear .negative case_50_39_24).check 50 39 24 = true := by
  change case_50_39_24.check 50 39 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_39_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_39_25_checked :
    (Witness.linear .negative case_50_39_25).check 50 39 25 = true := by
  change case_50_39_25.check 50 39 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_40_1_checked :
    (Witness.rising).check 50 40 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_40_2_checked :
    (Witness.rising).check 50 40 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_40_3_checked :
    (Witness.rising).check 50 40 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_40_4_checked :
    (Witness.rising).check 50 40 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_40_5_checked :
    (Witness.rising).check 50 40 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_40_6_checked :
    (Witness.rising).check 50 40 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_40_7_checked :
    (Witness.rising).check 50 40 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_40_8_checked :
    (Witness.rising).check 50 40 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_40_9_checked :
    (Witness.rising).check 50 40 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_40_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_50_40_10_checked :
    (Witness.linear .positive case_50_40_10).check 50 40 10 = true := by
  change case_50_40_10.check 50 40 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_40_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_50_40_11_checked :
    (Witness.linear .positive case_50_40_11).check 50 40 11 = true := by
  change case_50_40_11.check 50 40 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_40_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_50_40_12_checked :
    (Witness.linear .positive case_50_40_12).check 50 40 12 = true := by
  change case_50_40_12.check 50 40 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_40_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_50_40_13_checked :
    (Witness.linear .positive case_50_40_13).check 50 40 13 = true := by
  change case_50_40_13.check 50 40 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_40_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_50_40_14_checked :
    (Witness.linear .positive case_50_40_14).check 50 40 14 = true := by
  change case_50_40_14.check 50 40 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_40_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_50_40_15_checked :
    (Witness.linear .positive case_50_40_15).check 50 40 15 = true := by
  change case_50_40_15.check 50 40 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_40_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_50_40_16_checked :
    (Witness.linear .positive case_50_40_16).check 50 40 16 = true := by
  change case_50_40_16.check 50 40 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_40_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_50_40_17_checked :
    (Witness.linear .positive case_50_40_17).check 50 40 17 = true := by
  change case_50_40_17.check 50 40 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_40_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_50_40_18_checked :
    (Witness.linear .positive case_50_40_18).check 50 40 18 = true := by
  change case_50_40_18.check 50 40 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_40_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_50_40_19_checked :
    (Witness.linear .positive case_50_40_19).check 50 40 19 = true := by
  change case_50_40_19.check 50 40 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_40_20 : Certificate := {
  objectiveScale := 27
  eta := 1059489480
  rows := #[⟨.assumptionRow 20, 35⟩]
  caps := #[0, 0, 303951900, 91815885, 27865305, 8506205, 2615008, 810730, 253878, 112896420, 112896420] }

theorem case_50_40_20_checked :
    (Witness.linear .conditional case_50_40_20).check 50 40 20 = true := by
  change case_50_40_20.check 50 40 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_40_21 : Certificate := {
  objectiveScale := 998
  eta := 11267310840
  rows := #[⟨.assumptionRow 21, 887⟩]
  caps := #[0, 0, 3731955045, 1203621510, 380882645, 127794095, 45272326, 27293640, 15971741880, 14932722630, 9997706355] }

theorem case_50_40_21_checked :
    (Witness.linear .conditional case_50_40_21).check 50 40 21 = true := by
  change case_50_40_21.check 50 40 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_40_22 : Certificate := {
  objectiveScale := 32
  eta := 28484235
  rows := #[⟨.assumptionRow 22, 19⟩]
  caps := #[0, 0, 10607025, 4242810, 1701425, 629717, 277761, 100776, 660009840, 648223950, 459079425] }

theorem case_50_40_22_checked :
    (Witness.linear .conditional case_50_40_22).check 50 40 22 = true := by
  change case_50_40_22.check 50 40 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_40_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 35357670, 35357670, 25662825] }

theorem case_50_40_23_checked :
    (Witness.linear .negative case_50_40_23).check 50 40 23 = true := by
  change case_50_40_23.check 50 40 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_40_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9694845] }

theorem case_50_40_24_checked :
    (Witness.linear .negative case_50_40_24).check 50 40 24 = true := by
  change case_50_40_24.check 50 40 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_40_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_40_25_checked :
    (Witness.linear .negative case_50_40_25).check 50 40 25 = true := by
  change case_50_40_25.check 50 40 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_40_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_40_26_checked :
    (Witness.linear .negative case_50_40_26).check 50 40 26 = true := by
  change case_50_40_26.check 50 40 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_41_1_checked :
    (Witness.rising).check 50 41 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_41_2_checked :
    (Witness.rising).check 50 41 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_41_3_checked :
    (Witness.rising).check 50 41 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_41_4_checked :
    (Witness.rising).check 50 41 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_41_5_checked :
    (Witness.rising).check 50 41 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_41_6_checked :
    (Witness.rising).check 50 41 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_41_7_checked :
    (Witness.rising).check 50 41 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_41_8_checked :
    (Witness.rising).check 50 41 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_41_9_checked :
    (Witness.rising).check 50 41 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_41_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_50_41_10_checked :
    (Witness.linear .positive case_50_41_10).check 50 41 10 = true := by
  change case_50_41_10.check 50 41 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_41_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_50_41_11_checked :
    (Witness.linear .positive case_50_41_11).check 50 41 11 = true := by
  change case_50_41_11.check 50 41 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_41_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_50_41_12_checked :
    (Witness.linear .positive case_50_41_12).check 50 41 12 = true := by
  change case_50_41_12.check 50 41 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_41_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_50_41_13_checked :
    (Witness.linear .positive case_50_41_13).check 50 41 13 = true := by
  change case_50_41_13.check 50 41 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_41_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_50_41_14_checked :
    (Witness.linear .positive case_50_41_14).check 50 41 14 = true := by
  change case_50_41_14.check 50 41 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_41_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_50_41_15_checked :
    (Witness.linear .positive case_50_41_15).check 50 41 15 = true := by
  change case_50_41_15.check 50 41 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_41_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_50_41_16_checked :
    (Witness.linear .positive case_50_41_16).check 50 41 16 = true := by
  change case_50_41_16.check 50 41 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_41_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_50_41_17_checked :
    (Witness.linear .positive case_50_41_17).check 50 41 17 = true := by
  change case_50_41_17.check 50 41 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_41_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_50_41_18_checked :
    (Witness.linear .positive case_50_41_18).check 50 41 18 = true := by
  change case_50_41_18.check 50 41 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_41_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_50_41_19_checked :
    (Witness.linear .positive case_50_41_19).check 50 41 19 = true := by
  change case_50_41_19.check 50 41 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_41_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_50_41_20_checked :
    (Witness.linear .positive case_50_41_20).check 50 41 20 = true := by
  change case_50_41_20.check 50 41 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_41_21 : Certificate := {
  objectiveScale := 1
  eta := 27293640
  rows := #[⟨.assumptionRow 21, 1⟩]
  caps := #[0, 0, 8684340, 2731365, 852150, 264385, 81719, 28424, 27293640, 24812400] }

theorem case_50_41_21_checked :
    (Witness.linear .conditional case_50_41_21).check 50 41 21 = true := by
  change case_50_41_21.check 50 41 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_41_22 : Certificate := {
  objectiveScale := 17
  eta := 13656825
  rows := #[⟨.assumptionRow 22, 10⟩]
  caps := #[0, 0, 5278845, 2022735, 847550, 298034, 138567, 1275977670, 1255507440, 893246400] }

theorem case_50_41_22_checked :
    (Witness.linear .conditional case_50_41_22).check 50 41 22 = true := by
  change case_50_41_22.check 50 41 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_41_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 129644790, 129644790, 94287120] }

theorem case_50_41_23_checked :
    (Witness.linear .negative case_50_41_23).check 50 41 23 = true := by
  change case_50_41_23.check 50 41 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_41_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 35357670] }

theorem case_50_41_24_checked :
    (Witness.linear .negative case_50_41_24).check 50 41 24 = true := by
  change case_50_41_24.check 50 41 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_41_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_41_25_checked :
    (Witness.linear .negative case_50_41_25).check 50 41 25 = true := by
  change case_50_41_25.check 50 41 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_41_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_41_26_checked :
    (Witness.linear .negative case_50_41_26).check 50 41 26 = true := by
  change case_50_41_26.check 50 41 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_42_1_checked :
    (Witness.rising).check 50 42 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_42_2_checked :
    (Witness.rising).check 50 42 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_42_3_checked :
    (Witness.rising).check 50 42 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_42_4_checked :
    (Witness.rising).check 50 42 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_42_5_checked :
    (Witness.rising).check 50 42 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_42_6_checked :
    (Witness.rising).check 50 42 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_42_7_checked :
    (Witness.rising).check 50 42 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_42_8_checked :
    (Witness.rising).check 50 42 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_42_9_checked :
    (Witness.rising).check 50 42 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_42_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1] }

theorem case_50_42_10_checked :
    (Witness.linear .positive case_50_42_10).check 50 42 10 = true := by
  change case_50_42_10.check 50 42 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_42_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_50_42_11_checked :
    (Witness.linear .positive case_50_42_11).check 50 42 11 = true := by
  change case_50_42_11.check 50 42 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_42_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_50_42_12_checked :
    (Witness.linear .positive case_50_42_12).check 50 42 12 = true := by
  change case_50_42_12.check 50 42 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_42_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_50_42_13_checked :
    (Witness.linear .positive case_50_42_13).check 50 42 13 = true := by
  change case_50_42_13.check 50 42 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_42_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_50_42_14_checked :
    (Witness.linear .positive case_50_42_14).check 50 42 14 = true := by
  change case_50_42_14.check 50 42 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_42_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_50_42_15_checked :
    (Witness.linear .positive case_50_42_15).check 50 42 15 = true := by
  change case_50_42_15.check 50 42 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_42_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_50_42_16_checked :
    (Witness.linear .positive case_50_42_16).check 50 42 16 = true := by
  change case_50_42_16.check 50 42 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_42_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_50_42_17_checked :
    (Witness.linear .positive case_50_42_17).check 50 42 17 = true := by
  change case_50_42_17.check 50 42 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_42_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_50_42_18_checked :
    (Witness.linear .positive case_50_42_18).check 50 42 18 = true := by
  change case_50_42_18.check 50 42 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_42_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_50_42_19_checked :
    (Witness.linear .positive case_50_42_19).check 50 42 19 = true := by
  change case_50_42_19.check 50 42 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_42_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_50_42_20_checked :
    (Witness.linear .positive case_50_42_20).check 50 42 20 = true := by
  change case_50_42_20.check 50 42 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_42_21 : Certificate := {
  objectiveScale := 10
  eta := 4523920830
  rows := #[⟨.assumptionRow 21, 17⟩]
  caps := #[0, 0, 1275977670, 362261040, 103601775, 29871135, 8691930, 2555576, 760342] }

theorem case_50_42_21_checked :
    (Witness.linear .conditional case_50_42_21).check 50 42 21 = true := by
  change case_50_42_21.check 50 42 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_42_22 : Certificate := {
  objectiveScale := 537
  eta := 3870734400
  rows := #[⟨.assumptionRow 22, 398⟩]
  caps := #[0, 0, 1332515925, 434098665, 167640330, 59967325, 20470230, 66698832750, 64494871320] }

theorem case_50_42_22_checked :
    (Witness.linear .conditional case_50_42_22).check 50 42 22 = true := by
  change case_50_42_22.check 50 42 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_42_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 477638700, 477638700, 347993910] }

theorem case_50_42_23_checked :
    (Witness.linear .negative case_50_42_23).check 50 42 23 = true := by
  change case_50_42_23.check 50 42 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_42_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 129644790] }

theorem case_50_42_24_checked :
    (Witness.linear .negative case_50_42_24).check 50 42 24 = true := by
  change case_50_42_24.check 50 42 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_42_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_42_25_checked :
    (Witness.linear .negative case_50_42_25).check 50 42 25 = true := by
  change case_50_42_25.check 50 42 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_42_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_42_26_checked :
    (Witness.linear .negative case_50_42_26).check 50 42 26 = true := by
  change case_50_42_26.check 50 42 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_42_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_42_27_checked :
    (Witness.linear .negative case_50_42_27).check 50 42 27 = true := by
  change case_50_42_27.check 50 42 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_43_1_checked :
    (Witness.rising).check 50 43 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_43_2_checked :
    (Witness.rising).check 50 43 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_43_3_checked :
    (Witness.rising).check 50 43 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_43_4_checked :
    (Witness.rising).check 50 43 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_43_5_checked :
    (Witness.rising).check 50 43 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_43_6_checked :
    (Witness.rising).check 50 43 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_43_7_checked :
    (Witness.rising).check 50 43 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_43_8_checked :
    (Witness.rising).check 50 43 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_43_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1] }

theorem case_50_43_9_checked :
    (Witness.linear .positive case_50_43_9).check 50 43 9 = true := by
  change case_50_43_9.check 50 43 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_43_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2] }

theorem case_50_43_10_checked :
    (Witness.linear .positive case_50_43_10).check 50 43 10 = true := by
  change case_50_43_10.check 50 43 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_43_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5] }

theorem case_50_43_11_checked :
    (Witness.linear .positive case_50_43_11).check 50 43 11 = true := by
  change case_50_43_11.check 50 43 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_43_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14] }

theorem case_50_43_12_checked :
    (Witness.linear .positive case_50_43_12).check 50 43 12 = true := by
  change case_50_43_12.check 50 43 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_43_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42] }

theorem case_50_43_13_checked :
    (Witness.linear .positive case_50_43_13).check 50 43 13 = true := by
  change case_50_43_13.check 50 43 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_43_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_50_43_14_checked :
    (Witness.linear .positive case_50_43_14).check 50 43 14 = true := by
  change case_50_43_14.check 50 43 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_43_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_50_43_15_checked :
    (Witness.linear .positive case_50_43_15).check 50 43 15 = true := by
  change case_50_43_15.check 50 43 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_43_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_50_43_16_checked :
    (Witness.linear .positive case_50_43_16).check 50 43 16 = true := by
  change case_50_43_16.check 50 43 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_43_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_50_43_17_checked :
    (Witness.linear .positive case_50_43_17).check 50 43 17 = true := by
  change case_50_43_17.check 50 43 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_43_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_50_43_18_checked :
    (Witness.linear .positive case_50_43_18).check 50 43 18 = true := by
  change case_50_43_18.check 50 43 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_43_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_50_43_19_checked :
    (Witness.linear .positive case_50_43_19).check 50 43 19 = true := by
  change case_50_43_19.check 50 43 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_43_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_50_43_20_checked :
    (Witness.linear .positive case_50_43_20).check 50 43 20 = true := by
  change case_50_43_20.check 50 43 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_43_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900] }

theorem case_50_43_21_checked :
    (Witness.linear .positive case_50_43_21).check 50 43 21 = true := by
  change case_50_43_21.check 50 43 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_43_22 : Certificate := {
  objectiveScale := 692
  eta := 18748249440
  rows := #[⟨.assumptionRow 22, 597⟩]
  caps := #[0, 0, 5798037570, 2013016005, 683971470, 224655145, 72061737, 146410528680] }

theorem case_50_43_22_checked :
    (Witness.linear .conditional case_50_43_22).check 50 43 22 = true := by
  change case_50_43_22.check 50 43 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_43_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 1767263190, 1767263190, 1289624490] }

theorem case_50_43_23_checked :
    (Witness.linear .negative case_50_43_23).check 50 43 23 = true := by
  change case_50_43_23.check 50 43 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_43_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 477638700] }

theorem case_50_43_24_checked :
    (Witness.linear .negative case_50_43_24).check 50 43 24 = true := by
  change case_50_43_24.check 50 43 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_43_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_43_25_checked :
    (Witness.linear .negative case_50_43_25).check 50 43 25 = true := by
  change case_50_43_25.check 50 43 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_43_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_43_26_checked :
    (Witness.linear .negative case_50_43_26).check 50 43 26 = true := by
  change case_50_43_26.check 50 43 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_43_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_43_27_checked :
    (Witness.linear .negative case_50_43_27).check 50 43 27 = true := by
  change case_50_43_27.check 50 43 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_43_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_50_43_28_checked :
    (Witness.linear .negative case_50_43_28).check 50 43 28 = true := by
  change case_50_43_28.check 50 43 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_44_1_checked :
    (Witness.rising).check 50 44 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_44_2_checked :
    (Witness.rising).check 50 44 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_44_3_checked :
    (Witness.rising).check 50 44 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_44_4_checked :
    (Witness.rising).check 50 44 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_44_5_checked :
    (Witness.rising).check 50 44 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_44_6_checked :
    (Witness.rising).check 50 44 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_44_7_checked :
    (Witness.rising).check 50 44 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_44_8_checked :
    (Witness.rising).check 50 44 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_44_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2] }

theorem case_50_44_9_checked :
    (Witness.linear .positive case_50_44_9).check 50 44 9 = true := by
  change case_50_44_9.check 50 44 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_44_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_50_44_10_checked :
    (Witness.linear .positive case_50_44_10).check 50 44 10 = true := by
  change case_50_44_10.check 50 44 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_44_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14] }

theorem case_50_44_11_checked :
    (Witness.linear .positive case_50_44_11).check 50 44 11 = true := by
  change case_50_44_11.check 50 44 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_44_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42] }

theorem case_50_44_12_checked :
    (Witness.linear .positive case_50_44_12).check 50 44 12 = true := by
  change case_50_44_12.check 50 44 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_44_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132] }

theorem case_50_44_13_checked :
    (Witness.linear .positive case_50_44_13).check 50 44 13 = true := by
  change case_50_44_13.check 50 44 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_44_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429] }

theorem case_50_44_14_checked :
    (Witness.linear .positive case_50_44_14).check 50 44 14 = true := by
  change case_50_44_14.check 50 44 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_44_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430] }

theorem case_50_44_15_checked :
    (Witness.linear .positive case_50_44_15).check 50 44 15 = true := by
  change case_50_44_15.check 50 44 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_44_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862] }

theorem case_50_44_16_checked :
    (Witness.linear .positive case_50_44_16).check 50 44 16 = true := by
  change case_50_44_16.check 50 44 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_44_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796] }

theorem case_50_44_17_checked :
    (Witness.linear .positive case_50_44_17).check 50 44 17 = true := by
  change case_50_44_17.check 50 44 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_44_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_50_44_18_checked :
    (Witness.linear .positive case_50_44_18).check 50 44 18 = true := by
  change case_50_44_18.check 50 44 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_44_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_50_44_19_checked :
    (Witness.linear .positive case_50_44_19).check 50 44 19 = true := by
  change case_50_44_19.check 50 44 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_44_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900] }

theorem case_50_44_20_checked :
    (Witness.linear .positive case_50_44_20).check 50 44 20 = true := by
  change case_50_44_20.check 50 44 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_44_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440] }

theorem case_50_44_21_checked :
    (Witness.linear .positive case_50_44_21).check 50 44 21 = true := by
  change case_50_44_21.check 50 44 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_44_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670, 9694845] }

theorem case_50_44_22_checked :
    (Witness.linear .positive case_50_44_22).check 50 44 22 = true := by
  change case_50_44_22.check 50 44 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_44_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 6564120420, 6564120420, 4796857230] }

theorem case_50_44_23_checked :
    (Witness.linear .negative case_50_44_23).check 50 44 23 = true := by
  change case_50_44_23.check 50 44 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_44_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 1767263190] }

theorem case_50_44_24_checked :
    (Witness.linear .negative case_50_44_24).check 50 44 24 = true := by
  change case_50_44_24.check 50 44 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_44_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_50_44_25_checked :
    (Witness.linear .negative case_50_44_25).check 50 44 25 = true := by
  change case_50_44_25.check 50 44 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_44_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_50_44_26_checked :
    (Witness.linear .negative case_50_44_26).check 50 44 26 = true := by
  change case_50_44_26.check 50 44 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_44_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_50_44_27_checked :
    (Witness.linear .negative case_50_44_27).check 50 44 27 = true := by
  change case_50_44_27.check 50 44 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_44_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_50_44_28_checked :
    (Witness.linear .negative case_50_44_28).check 50 44 28 = true := by
  change case_50_44_28.check 50 44 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_45_1_checked :
    (Witness.rising).check 50 45 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_45_2_checked :
    (Witness.rising).check 50 45 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_45_3_checked :
    (Witness.rising).check 50 45 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_45_4_checked :
    (Witness.rising).check 50 45 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_45_5_checked :
    (Witness.rising).check 50 45 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_45_6_checked :
    (Witness.rising).check 50 45 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_45_7_checked :
    (Witness.rising).check 50 45 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_45_8_checked :
    (Witness.rising).check 50 45 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_45_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5] }

theorem case_50_45_9_checked :
    (Witness.linear .positive case_50_45_9).check 50 45 9 = true := by
  change case_50_45_9.check 50 45 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_45_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_50_45_10_checked :
    (Witness.linear .positive case_50_45_10).check 50 45 10 = true := by
  change case_50_45_10.check 50 45 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_45_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_50_45_11_checked :
    (Witness.linear .positive case_50_45_11).check 50 45 11 = true := by
  change case_50_45_11.check 50 45 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_45_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132] }

theorem case_50_45_12_checked :
    (Witness.linear .positive case_50_45_12).check 50 45 12 = true := by
  change case_50_45_12.check 50 45 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_45_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429] }

theorem case_50_45_13_checked :
    (Witness.linear .positive case_50_45_13).check 50 45 13 = true := by
  change case_50_45_13.check 50 45 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_45_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430] }

theorem case_50_45_14_checked :
    (Witness.linear .positive case_50_45_14).check 50 45 14 = true := by
  change case_50_45_14.check 50 45 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_45_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862] }

theorem case_50_45_15_checked :
    (Witness.linear .positive case_50_45_15).check 50 45 15 = true := by
  change case_50_45_15.check 50 45 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_45_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796] }

theorem case_50_45_16_checked :
    (Witness.linear .positive case_50_45_16).check 50 45 16 = true := by
  change case_50_45_16.check 50 45 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_45_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786] }

theorem case_50_45_17_checked :
    (Witness.linear .positive case_50_45_17).check 50 45 17 = true := by
  change case_50_45_17.check 50 45 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_45_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012] }

theorem case_50_45_18_checked :
    (Witness.linear .positive case_50_45_18).check 50 45 18 = true := by
  change case_50_45_18.check 50 45 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_45_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900] }

theorem case_50_45_19_checked :
    (Witness.linear .positive case_50_45_19).check 50 45 19 = true := by
  change case_50_45_19.check 50 45 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_45_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440] }

theorem case_50_45_20_checked :
    (Witness.linear .positive case_50_45_20).check 50 45 20 = true := by
  change case_50_45_20.check 50 45 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_45_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845] }

theorem case_50_45_21_checked :
    (Witness.linear .positive case_50_45_21).check 50 45 21 = true := by
  change case_50_45_21.check 50 45 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_45_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670] }

theorem case_50_45_22_checked :
    (Witness.linear .positive case_50_45_22).check 50 45 22 = true := by
  change case_50_45_22.check 50 45 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_45_23 : Certificate := {
  objectiveScale := 939
  eta := 15177205680
  rows := #[⟨.assumptionRow 23, 682⟩]
  caps := #[0, 0, 5419028160, 1987263135, 672386715, 259451400] }

theorem case_50_45_23_checked :
    (Witness.linear .conditional case_50_45_23).check 50 45 23 = true := by
  change case_50_45_23.check 50 45 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_45_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 6564120420] }

theorem case_50_45_24_checked :
    (Witness.linear .negative case_50_45_24).check 50 45 24 = true := by
  change case_50_45_24.check 50 45 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_45_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_50_45_25_checked :
    (Witness.linear .negative case_50_45_25).check 50 45 25 = true := by
  change case_50_45_25.check 50 45 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_45_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_50_45_26_checked :
    (Witness.linear .negative case_50_45_26).check 50 45 26 = true := by
  change case_50_45_26.check 50 45 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_45_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_50_45_27_checked :
    (Witness.linear .negative case_50_45_27).check 50 45 27 = true := by
  change case_50_45_27.check 50 45 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_45_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_50_45_28_checked :
    (Witness.linear .negative case_50_45_28).check 50 45 28 = true := by
  change case_50_45_28.check 50 45 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_45_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_50_45_29_checked :
    (Witness.linear .negative case_50_45_29).check 50 45 29 = true := by
  change case_50_45_29.check 50 45 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_46_1_checked :
    (Witness.rising).check 50 46 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_46_2_checked :
    (Witness.rising).check 50 46 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_46_3_checked :
    (Witness.rising).check 50 46 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_46_4_checked :
    (Witness.rising).check 50 46 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_46_5_checked :
    (Witness.rising).check 50 46 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_46_6_checked :
    (Witness.rising).check 50 46 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_46_7_checked :
    (Witness.rising).check 50 46 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_46_8_checked :
    (Witness.rising).check 50 46 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_46_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14] }

theorem case_50_46_9_checked :
    (Witness.linear .positive case_50_46_9).check 50 46 9 = true := by
  change case_50_46_9.check 50 46 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_46_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_50_46_10_checked :
    (Witness.linear .positive case_50_46_10).check 50 46 10 = true := by
  change case_50_46_10.check 50 46 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_46_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_50_46_11_checked :
    (Witness.linear .positive case_50_46_11).check 50 46 11 = true := by
  change case_50_46_11.check 50 46 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_46_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429] }

theorem case_50_46_12_checked :
    (Witness.linear .positive case_50_46_12).check 50 46 12 = true := by
  change case_50_46_12.check 50 46 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_46_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430] }

theorem case_50_46_13_checked :
    (Witness.linear .positive case_50_46_13).check 50 46 13 = true := by
  change case_50_46_13.check 50 46 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_46_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862] }

theorem case_50_46_14_checked :
    (Witness.linear .positive case_50_46_14).check 50 46 14 = true := by
  change case_50_46_14.check 50 46 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_46_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796] }

theorem case_50_46_15_checked :
    (Witness.linear .positive case_50_46_15).check 50 46 15 = true := by
  change case_50_46_15.check 50 46 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_46_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786] }

theorem case_50_46_16_checked :
    (Witness.linear .positive case_50_46_16).check 50 46 16 = true := by
  change case_50_46_16.check 50 46 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_46_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012] }

theorem case_50_46_17_checked :
    (Witness.linear .positive case_50_46_17).check 50 46 17 = true := by
  change case_50_46_17.check 50 46 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_46_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900] }

theorem case_50_46_18_checked :
    (Witness.linear .positive case_50_46_18).check 50 46 18 = true := by
  change case_50_46_18.check 50 46 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_46_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440] }

theorem case_50_46_19_checked :
    (Witness.linear .positive case_50_46_19).check 50 46 19 = true := by
  change case_50_46_19.check 50 46 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_46_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845] }

theorem case_50_46_20_checked :
    (Witness.linear .positive case_50_46_20).check 50 46 20 = true := by
  change case_50_46_20.check 50 46 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_46_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670] }

theorem case_50_46_21_checked :
    (Witness.linear .positive case_50_46_21).check 50 46 21 = true := by
  change case_50_46_21.check 50 46 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_46_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790] }

theorem case_50_46_22_checked :
    (Witness.linear .positive case_50_46_22).check 50 46 22 = true := by
  change case_50_46_22.check 50 46 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_46_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700] }

theorem case_50_46_23_checked :
    (Witness.linear .positive case_50_46_23).check 50 46 23 = true := by
  change case_50_46_23.check 50 46 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_46_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 24466267020] }

theorem case_50_46_24_checked :
    (Witness.linear .negative case_50_46_24).check 50 46 24 = true := by
  change case_50_46_24.check 50 46 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_46_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_50_46_25_checked :
    (Witness.linear .negative case_50_46_25).check 50 46 25 = true := by
  change case_50_46_25.check 50 46 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_46_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_50_46_26_checked :
    (Witness.linear .negative case_50_46_26).check 50 46 26 = true := by
  change case_50_46_26.check 50 46 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_46_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_50_46_27_checked :
    (Witness.linear .negative case_50_46_27).check 50 46 27 = true := by
  change case_50_46_27.check 50 46 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_46_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_50_46_28_checked :
    (Witness.linear .negative case_50_46_28).check 50 46 28 = true := by
  change case_50_46_28.check 50 46 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_46_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_50_46_29_checked :
    (Witness.linear .negative case_50_46_29).check 50 46 29 = true := by
  change case_50_46_29.check 50 46 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_46_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_50_46_30_checked :
    (Witness.linear .negative case_50_46_30).check 50 46 30 = true := by
  change case_50_46_30.check 50 46 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_47_1_checked :
    (Witness.rising).check 50 47 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_47_2_checked :
    (Witness.rising).check 50 47 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_47_3_checked :
    (Witness.rising).check 50 47 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_47_4_checked :
    (Witness.rising).check 50 47 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_47_5_checked :
    (Witness.rising).check 50 47 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_47_6_checked :
    (Witness.rising).check 50 47 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_47_7_checked :
    (Witness.rising).check 50 47 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_47_8_checked :
    (Witness.rising).check 50 47 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_47_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_50_47_9_checked :
    (Witness.linear .positive case_50_47_9).check 50 47 9 = true := by
  change case_50_47_9.check 50 47 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_47_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_50_47_10_checked :
    (Witness.linear .positive case_50_47_10).check 50 47 10 = true := by
  change case_50_47_10.check 50 47 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_47_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_50_47_11_checked :
    (Witness.linear .positive case_50_47_11).check 50 47 11 = true := by
  change case_50_47_11.check 50 47 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_47_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_50_47_12_checked :
    (Witness.linear .positive case_50_47_12).check 50 47 12 = true := by
  change case_50_47_12.check 50 47 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_47_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862] }

theorem case_50_47_13_checked :
    (Witness.linear .positive case_50_47_13).check 50 47 13 = true := by
  change case_50_47_13.check 50 47 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_47_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796] }

theorem case_50_47_14_checked :
    (Witness.linear .positive case_50_47_14).check 50 47 14 = true := by
  change case_50_47_14.check 50 47 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_47_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786] }

theorem case_50_47_15_checked :
    (Witness.linear .positive case_50_47_15).check 50 47 15 = true := by
  change case_50_47_15.check 50 47 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_47_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012] }

theorem case_50_47_16_checked :
    (Witness.linear .positive case_50_47_16).check 50 47 16 = true := by
  change case_50_47_16.check 50 47 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_47_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900] }

theorem case_50_47_17_checked :
    (Witness.linear .positive case_50_47_17).check 50 47 17 = true := by
  change case_50_47_17.check 50 47 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_47_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440] }

theorem case_50_47_18_checked :
    (Witness.linear .positive case_50_47_18).check 50 47 18 = true := by
  change case_50_47_18.check 50 47 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_47_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845] }

theorem case_50_47_19_checked :
    (Witness.linear .positive case_50_47_19).check 50 47 19 = true := by
  change case_50_47_19.check 50 47 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_47_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670] }

theorem case_50_47_20_checked :
    (Witness.linear .positive case_50_47_20).check 50 47 20 = true := by
  change case_50_47_20.check 50 47 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_47_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790] }

theorem case_50_47_21_checked :
    (Witness.linear .positive case_50_47_21).check 50 47 21 = true := by
  change case_50_47_21.check 50 47 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_47_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700] }

theorem case_50_47_22_checked :
    (Witness.linear .positive case_50_47_22).check 50 47 22 = true := by
  change case_50_47_22.check 50 47 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_47_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190] }

theorem case_50_47_23_checked :
    (Witness.linear .positive case_50_47_23).check 50 47 23 = true := by
  change case_50_47_23.check 50 47 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_47_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 91482563640] }

theorem case_50_47_24_checked :
    (Witness.linear .negative case_50_47_24).check 50 47 24 = true := by
  change case_50_47_24.check 50 47 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_47_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_50_47_25_checked :
    (Witness.linear .negative case_50_47_25).check 50 47 25 = true := by
  change case_50_47_25.check 50 47 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_47_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_50_47_26_checked :
    (Witness.linear .negative case_50_47_26).check 50 47 26 = true := by
  change case_50_47_26.check 50 47 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_47_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_50_47_27_checked :
    (Witness.linear .negative case_50_47_27).check 50 47 27 = true := by
  change case_50_47_27.check 50 47 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_47_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_50_47_28_checked :
    (Witness.linear .negative case_50_47_28).check 50 47 28 = true := by
  change case_50_47_28.check 50 47 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_47_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_50_47_29_checked :
    (Witness.linear .negative case_50_47_29).check 50 47 29 = true := by
  change case_50_47_29.check 50 47 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_47_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_50_47_30_checked :
    (Witness.linear .negative case_50_47_30).check 50 47 30 = true := by
  change case_50_47_30.check 50 47 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_48_1_checked :
    (Witness.rising).check 50 48 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_48_2_checked :
    (Witness.rising).check 50 48 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_48_3_checked :
    (Witness.rising).check 50 48 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_48_4_checked :
    (Witness.rising).check 50 48 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_48_5_checked :
    (Witness.rising).check 50 48 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_48_6_checked :
    (Witness.rising).check 50 48 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_48_7_checked :
    (Witness.rising).check 50 48 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_48_8_checked :
    (Witness.rising).check 50 48 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_48_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_50_48_9_checked :
    (Witness.linear .positive case_50_48_9).check 50 48 9 = true := by
  change case_50_48_9.check 50 48 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_48_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_50_48_10_checked :
    (Witness.linear .positive case_50_48_10).check 50 48 10 = true := by
  change case_50_48_10.check 50 48 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_48_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_50_48_11_checked :
    (Witness.linear .positive case_50_48_11).check 50 48 11 = true := by
  change case_50_48_11.check 50 48 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_48_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_50_48_12_checked :
    (Witness.linear .positive case_50_48_12).check 50 48 12 = true := by
  change case_50_48_12.check 50 48 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_48_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796] }

theorem case_50_48_13_checked :
    (Witness.linear .positive case_50_48_13).check 50 48 13 = true := by
  change case_50_48_13.check 50 48 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_48_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786] }

theorem case_50_48_14_checked :
    (Witness.linear .positive case_50_48_14).check 50 48 14 = true := by
  change case_50_48_14.check 50 48 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_48_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012] }

theorem case_50_48_15_checked :
    (Witness.linear .positive case_50_48_15).check 50 48 15 = true := by
  change case_50_48_15.check 50 48 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_48_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900] }

theorem case_50_48_16_checked :
    (Witness.linear .positive case_50_48_16).check 50 48 16 = true := by
  change case_50_48_16.check 50 48 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_48_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440] }

theorem case_50_48_17_checked :
    (Witness.linear .positive case_50_48_17).check 50 48 17 = true := by
  change case_50_48_17.check 50 48 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_48_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845] }

theorem case_50_48_18_checked :
    (Witness.linear .positive case_50_48_18).check 50 48 18 = true := by
  change case_50_48_18.check 50 48 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_48_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670] }

theorem case_50_48_19_checked :
    (Witness.linear .positive case_50_48_19).check 50 48 19 = true := by
  change case_50_48_19.check 50 48 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_48_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790] }

theorem case_50_48_20_checked :
    (Witness.linear .positive case_50_48_20).check 50 48 20 = true := by
  change case_50_48_20.check 50 48 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_48_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700] }

theorem case_50_48_21_checked :
    (Witness.linear .positive case_50_48_21).check 50 48 21 = true := by
  change case_50_48_21.check 50 48 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_48_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190] }

theorem case_50_48_22_checked :
    (Witness.linear .positive case_50_48_22).check 50 48 22 = true := by
  change case_50_48_22.check 50 48 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_48_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420] }

theorem case_50_48_23_checked :
    (Witness.linear .positive case_50_48_23).check 50 48 23 = true := by
  change case_50_48_23.check 50 48 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_48_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020] }

theorem case_50_48_24_checked :
    (Witness.linear .positive case_50_48_24).check 50 48 24 = true := by
  change case_50_48_24.check 50 48 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_48_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_50_48_25_checked :
    (Witness.linear .negative case_50_48_25).check 50 48 25 = true := by
  change case_50_48_25.check 50 48 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_48_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_50_48_26_checked :
    (Witness.linear .negative case_50_48_26).check 50 48 26 = true := by
  change case_50_48_26.check 50 48 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_48_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_50_48_27_checked :
    (Witness.linear .negative case_50_48_27).check 50 48 27 = true := by
  change case_50_48_27.check 50 48 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_48_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_50_48_28_checked :
    (Witness.linear .negative case_50_48_28).check 50 48 28 = true := by
  change case_50_48_28.check 50 48 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_48_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_50_48_29_checked :
    (Witness.linear .negative case_50_48_29).check 50 48 29 = true := by
  change case_50_48_29.check 50 48 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_48_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_50_48_30_checked :
    (Witness.linear .negative case_50_48_30).check 50 48 30 = true := by
  change case_50_48_30.check 50 48 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_48_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_50_48_31_checked :
    (Witness.linear .negative case_50_48_31).check 50 48 31 = true := by
  change case_50_48_31.check 50 48 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_49_1_checked :
    (Witness.rising).check 50 49 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_49_2_checked :
    (Witness.rising).check 50 49 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_49_3_checked :
    (Witness.rising).check 50 49 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_49_4_checked :
    (Witness.rising).check 50 49 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_49_5_checked :
    (Witness.rising).check 50 49 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_49_6_checked :
    (Witness.rising).check 50 49 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_49_7_checked :
    (Witness.rising).check 50 49 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_50_49_8_checked :
    (Witness.rising).check 50 49 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_49_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_50_49_9_checked :
    (Witness.linear .positive case_50_49_9).check 50 49 9 = true := by
  change case_50_49_9.check 50 49 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_49_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_50_49_10_checked :
    (Witness.linear .positive case_50_49_10).check 50 49 10 = true := by
  change case_50_49_10.check 50 49 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_49_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_50_49_11_checked :
    (Witness.linear .positive case_50_49_11).check 50 49 11 = true := by
  change case_50_49_11.check 50 49 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_49_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_50_49_12_checked :
    (Witness.linear .positive case_50_49_12).check 50 49 12 = true := by
  change case_50_49_12.check 50 49 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_49_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_50_49_13_checked :
    (Witness.linear .positive case_50_49_13).check 50 49 13 = true := by
  change case_50_49_13.check 50 49 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_49_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0] }

theorem case_50_49_14_checked :
    (Witness.linear .positive case_50_49_14).check 50 49 14 = true := by
  change case_50_49_14.check 50 49 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_49_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0] }

theorem case_50_49_15_checked :
    (Witness.linear .positive case_50_49_15).check 50 49 15 = true := by
  change case_50_49_15.check 50 49 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_49_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0] }

theorem case_50_49_16_checked :
    (Witness.linear .positive case_50_49_16).check 50 49 16 = true := by
  change case_50_49_16.check 50 49 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_49_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0] }

theorem case_50_49_17_checked :
    (Witness.linear .positive case_50_49_17).check 50 49 17 = true := by
  change case_50_49_17.check 50 49 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_49_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0] }

theorem case_50_49_18_checked :
    (Witness.linear .positive case_50_49_18).check 50 49 18 = true := by
  change case_50_49_18.check 50 49 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_49_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0] }

theorem case_50_49_19_checked :
    (Witness.linear .positive case_50_49_19).check 50 49 19 = true := by
  change case_50_49_19.check 50 49 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_49_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0] }

theorem case_50_49_20_checked :
    (Witness.linear .positive case_50_49_20).check 50 49 20 = true := by
  change case_50_49_20.check 50 49 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_49_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0] }

theorem case_50_49_21_checked :
    (Witness.linear .positive case_50_49_21).check 50 49 21 = true := by
  change case_50_49_21.check 50 49 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_49_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0] }

theorem case_50_49_22_checked :
    (Witness.linear .positive case_50_49_22).check 50 49 22 = true := by
  change case_50_49_22.check 50 49 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_49_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0] }

theorem case_50_49_23_checked :
    (Witness.linear .positive case_50_49_23).check 50 49 23 = true := by
  change case_50_49_23.check 50 49 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_49_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0] }

theorem case_50_49_24_checked :
    (Witness.linear .positive case_50_49_24).check 50 49 24 = true := by
  change case_50_49_24.check 50 49 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_49_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_50_49_25_checked :
    (Witness.linear .negative case_50_49_25).check 50 49 25 = true := by
  change case_50_49_25.check 50 49 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_49_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_50_49_26_checked :
    (Witness.linear .negative case_50_49_26).check 50 49 26 = true := by
  change case_50_49_26.check 50 49 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_49_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_50_49_27_checked :
    (Witness.linear .negative case_50_49_27).check 50 49 27 = true := by
  change case_50_49_27.check 50 49 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_49_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_50_49_28_checked :
    (Witness.linear .negative case_50_49_28).check 50 49 28 = true := by
  change case_50_49_28.check 50 49 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_49_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_50_49_29_checked :
    (Witness.linear .negative case_50_49_29).check 50 49 29 = true := by
  change case_50_49_29.check 50 49 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_49_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_50_49_30_checked :
    (Witness.linear .negative case_50_49_30).check 50 49 30 = true := by
  change case_50_49_30.check 50 49 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_49_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_50_49_31_checked :
    (Witness.linear .negative case_50_49_31).check 50 49 31 = true := by
  change case_50_49_31.check 50 49 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_50_49_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_50_49_32_checked :
    (Witness.linear .negative case_50_49_32).check 50 49 32 = true := by
  change case_50_49_32.check 50 49 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_50 (a k : ℕ) (h : Domain 50 a k) :
    ∃ w : Witness, w.check 50 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 25 ≤ a := by omega
  have haHi : a ≤ 49 := by omega
  interval_cases a

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_50_25_1_checked⟩

    · exact ⟨Witness.rising, case_50_25_2_checked⟩

    · exact ⟨Witness.rising, case_50_25_3_checked⟩

    · exact ⟨Witness.rising, case_50_25_4_checked⟩

    · exact ⟨Witness.rising, case_50_25_5_checked⟩

    · exact ⟨Witness.rising, case_50_25_6_checked⟩

    · exact ⟨Witness.rising, case_50_25_7_checked⟩

    · exact ⟨Witness.rising, case_50_25_8_checked⟩

    · exact ⟨Witness.rising, case_50_25_9_checked⟩

    · exact ⟨Witness.rising, case_50_25_10_checked⟩

    · exact ⟨Witness.linear .positive case_50_25_11, case_50_25_11_checked⟩

    · exact ⟨Witness.linear .positive case_50_25_12, case_50_25_12_checked⟩

    · exact ⟨Witness.linear .positive case_50_25_13, case_50_25_13_checked⟩

    · exact ⟨Witness.linear .positive case_50_25_14, case_50_25_14_checked⟩

    · exact ⟨Witness.linear .conditional case_50_25_15, case_50_25_15_checked⟩

    · exact ⟨Witness.linear .conditional case_50_25_16, case_50_25_16_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_50_26_1_checked⟩

    · exact ⟨Witness.rising, case_50_26_2_checked⟩

    · exact ⟨Witness.rising, case_50_26_3_checked⟩

    · exact ⟨Witness.rising, case_50_26_4_checked⟩

    · exact ⟨Witness.rising, case_50_26_5_checked⟩

    · exact ⟨Witness.rising, case_50_26_6_checked⟩

    · exact ⟨Witness.rising, case_50_26_7_checked⟩

    · exact ⟨Witness.rising, case_50_26_8_checked⟩

    · exact ⟨Witness.rising, case_50_26_9_checked⟩

    · exact ⟨Witness.rising, case_50_26_10_checked⟩

    · exact ⟨Witness.linear .positive case_50_26_11, case_50_26_11_checked⟩

    · exact ⟨Witness.linear .positive case_50_26_12, case_50_26_12_checked⟩

    · exact ⟨Witness.linear .positive case_50_26_13, case_50_26_13_checked⟩

    · exact ⟨Witness.linear .positive case_50_26_14, case_50_26_14_checked⟩

    · exact ⟨Witness.linear .conditional case_50_26_15, case_50_26_15_checked⟩

    · exact ⟨Witness.linear .conditional case_50_26_16, case_50_26_16_checked⟩

  · have hkHi : k ≤ 17 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_50_27_1_checked⟩

    · exact ⟨Witness.rising, case_50_27_2_checked⟩

    · exact ⟨Witness.rising, case_50_27_3_checked⟩

    · exact ⟨Witness.rising, case_50_27_4_checked⟩

    · exact ⟨Witness.rising, case_50_27_5_checked⟩

    · exact ⟨Witness.rising, case_50_27_6_checked⟩

    · exact ⟨Witness.rising, case_50_27_7_checked⟩

    · exact ⟨Witness.rising, case_50_27_8_checked⟩

    · exact ⟨Witness.rising, case_50_27_9_checked⟩

    · exact ⟨Witness.linear .positive case_50_27_10, case_50_27_10_checked⟩

    · exact ⟨Witness.linear .positive case_50_27_11, case_50_27_11_checked⟩

    · exact ⟨Witness.linear .positive case_50_27_12, case_50_27_12_checked⟩

    · exact ⟨Witness.linear .positive case_50_27_13, case_50_27_13_checked⟩

    · exact ⟨Witness.linear .positive case_50_27_14, case_50_27_14_checked⟩

    · exact ⟨Witness.linear .conditional case_50_27_15, case_50_27_15_checked⟩

    · exact ⟨Witness.linear .conditional case_50_27_16, case_50_27_16_checked⟩

    · exact ⟨Witness.linear .conditional case_50_27_17, case_50_27_17_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_50_28_1_checked⟩

    · exact ⟨Witness.rising, case_50_28_2_checked⟩

    · exact ⟨Witness.rising, case_50_28_3_checked⟩

    · exact ⟨Witness.rising, case_50_28_4_checked⟩

    · exact ⟨Witness.rising, case_50_28_5_checked⟩

    · exact ⟨Witness.rising, case_50_28_6_checked⟩

    · exact ⟨Witness.rising, case_50_28_7_checked⟩

    · exact ⟨Witness.rising, case_50_28_8_checked⟩

    · exact ⟨Witness.rising, case_50_28_9_checked⟩

    · exact ⟨Witness.linear .positive case_50_28_10, case_50_28_10_checked⟩

    · exact ⟨Witness.linear .positive case_50_28_11, case_50_28_11_checked⟩

    · exact ⟨Witness.linear .positive case_50_28_12, case_50_28_12_checked⟩

    · exact ⟨Witness.linear .positive case_50_28_13, case_50_28_13_checked⟩

    · exact ⟨Witness.linear .positive case_50_28_14, case_50_28_14_checked⟩

    · exact ⟨Witness.linear .conditional case_50_28_15, case_50_28_15_checked⟩

    · exact ⟨Witness.linear .conditional case_50_28_16, case_50_28_16_checked⟩

    · exact ⟨Witness.linear .conditional case_50_28_17, case_50_28_17_checked⟩

    · exact ⟨Witness.linear .negative case_50_28_18, case_50_28_18_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_50_29_1_checked⟩

    · exact ⟨Witness.rising, case_50_29_2_checked⟩

    · exact ⟨Witness.rising, case_50_29_3_checked⟩

    · exact ⟨Witness.rising, case_50_29_4_checked⟩

    · exact ⟨Witness.rising, case_50_29_5_checked⟩

    · exact ⟨Witness.rising, case_50_29_6_checked⟩

    · exact ⟨Witness.rising, case_50_29_7_checked⟩

    · exact ⟨Witness.rising, case_50_29_8_checked⟩

    · exact ⟨Witness.rising, case_50_29_9_checked⟩

    · exact ⟨Witness.linear .positive case_50_29_10, case_50_29_10_checked⟩

    · exact ⟨Witness.linear .positive case_50_29_11, case_50_29_11_checked⟩

    · exact ⟨Witness.linear .positive case_50_29_12, case_50_29_12_checked⟩

    · exact ⟨Witness.linear .positive case_50_29_13, case_50_29_13_checked⟩

    · exact ⟨Witness.linear .positive case_50_29_14, case_50_29_14_checked⟩

    · exact ⟨Witness.linear .conditional case_50_29_15, case_50_29_15_checked⟩

    · exact ⟨Witness.linear .conditional case_50_29_16, case_50_29_16_checked⟩

    · exact ⟨Witness.linear .conditional case_50_29_17, case_50_29_17_checked⟩

    · exact ⟨Witness.linear .conditional case_50_29_18, case_50_29_18_checked⟩

  · have hkHi : k ≤ 19 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_50_30_1_checked⟩

    · exact ⟨Witness.rising, case_50_30_2_checked⟩

    · exact ⟨Witness.rising, case_50_30_3_checked⟩

    · exact ⟨Witness.rising, case_50_30_4_checked⟩

    · exact ⟨Witness.rising, case_50_30_5_checked⟩

    · exact ⟨Witness.rising, case_50_30_6_checked⟩

    · exact ⟨Witness.rising, case_50_30_7_checked⟩

    · exact ⟨Witness.rising, case_50_30_8_checked⟩

    · exact ⟨Witness.rising, case_50_30_9_checked⟩

    · exact ⟨Witness.linear .positive case_50_30_10, case_50_30_10_checked⟩

    · exact ⟨Witness.linear .positive case_50_30_11, case_50_30_11_checked⟩

    · exact ⟨Witness.linear .positive case_50_30_12, case_50_30_12_checked⟩

    · exact ⟨Witness.linear .positive case_50_30_13, case_50_30_13_checked⟩

    · exact ⟨Witness.linear .positive case_50_30_14, case_50_30_14_checked⟩

    · exact ⟨Witness.linear .conditional case_50_30_15, case_50_30_15_checked⟩

    · exact ⟨Witness.linear .conditional case_50_30_16, case_50_30_16_checked⟩

    · exact ⟨Witness.linear .conditional case_50_30_17, case_50_30_17_checked⟩

    · exact ⟨Witness.linear .conditional case_50_30_18, case_50_30_18_checked⟩

    · exact ⟨Witness.linear .negative case_50_30_19, case_50_30_19_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_50_31_1_checked⟩

    · exact ⟨Witness.rising, case_50_31_2_checked⟩

    · exact ⟨Witness.rising, case_50_31_3_checked⟩

    · exact ⟨Witness.rising, case_50_31_4_checked⟩

    · exact ⟨Witness.rising, case_50_31_5_checked⟩

    · exact ⟨Witness.rising, case_50_31_6_checked⟩

    · exact ⟨Witness.rising, case_50_31_7_checked⟩

    · exact ⟨Witness.rising, case_50_31_8_checked⟩

    · exact ⟨Witness.rising, case_50_31_9_checked⟩

    · exact ⟨Witness.linear .positive case_50_31_10, case_50_31_10_checked⟩

    · exact ⟨Witness.linear .positive case_50_31_11, case_50_31_11_checked⟩

    · exact ⟨Witness.linear .positive case_50_31_12, case_50_31_12_checked⟩

    · exact ⟨Witness.linear .positive case_50_31_13, case_50_31_13_checked⟩

    · exact ⟨Witness.linear .positive case_50_31_14, case_50_31_14_checked⟩

    · exact ⟨Witness.linear .positive case_50_31_15, case_50_31_15_checked⟩

    · exact ⟨Witness.linear .conditional case_50_31_16, case_50_31_16_checked⟩

    · exact ⟨Witness.linear .conditional case_50_31_17, case_50_31_17_checked⟩

    · exact ⟨Witness.linear .conditional case_50_31_18, case_50_31_18_checked⟩

    · exact ⟨Witness.linear .negative case_50_31_19, case_50_31_19_checked⟩

    · exact ⟨Witness.linear .negative case_50_31_20, case_50_31_20_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_50_32_1_checked⟩

    · exact ⟨Witness.rising, case_50_32_2_checked⟩

    · exact ⟨Witness.rising, case_50_32_3_checked⟩

    · exact ⟨Witness.rising, case_50_32_4_checked⟩

    · exact ⟨Witness.rising, case_50_32_5_checked⟩

    · exact ⟨Witness.rising, case_50_32_6_checked⟩

    · exact ⟨Witness.rising, case_50_32_7_checked⟩

    · exact ⟨Witness.rising, case_50_32_8_checked⟩

    · exact ⟨Witness.rising, case_50_32_9_checked⟩

    · exact ⟨Witness.linear .positive case_50_32_10, case_50_32_10_checked⟩

    · exact ⟨Witness.linear .positive case_50_32_11, case_50_32_11_checked⟩

    · exact ⟨Witness.linear .positive case_50_32_12, case_50_32_12_checked⟩

    · exact ⟨Witness.linear .positive case_50_32_13, case_50_32_13_checked⟩

    · exact ⟨Witness.linear .positive case_50_32_14, case_50_32_14_checked⟩

    · exact ⟨Witness.linear .positive case_50_32_15, case_50_32_15_checked⟩

    · exact ⟨Witness.linear .conditional case_50_32_16, case_50_32_16_checked⟩

    · exact ⟨Witness.linear .conditional case_50_32_17, case_50_32_17_checked⟩

    · exact ⟨Witness.linear .conditional case_50_32_18, case_50_32_18_checked⟩

    · exact ⟨Witness.linear .conditional case_50_32_19, case_50_32_19_checked⟩

    · exact ⟨Witness.linear .negative case_50_32_20, case_50_32_20_checked⟩

  · have hkHi : k ≤ 21 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_50_33_1_checked⟩

    · exact ⟨Witness.rising, case_50_33_2_checked⟩

    · exact ⟨Witness.rising, case_50_33_3_checked⟩

    · exact ⟨Witness.rising, case_50_33_4_checked⟩

    · exact ⟨Witness.rising, case_50_33_5_checked⟩

    · exact ⟨Witness.rising, case_50_33_6_checked⟩

    · exact ⟨Witness.rising, case_50_33_7_checked⟩

    · exact ⟨Witness.rising, case_50_33_8_checked⟩

    · exact ⟨Witness.rising, case_50_33_9_checked⟩

    · exact ⟨Witness.linear .positive case_50_33_10, case_50_33_10_checked⟩

    · exact ⟨Witness.linear .positive case_50_33_11, case_50_33_11_checked⟩

    · exact ⟨Witness.linear .positive case_50_33_12, case_50_33_12_checked⟩

    · exact ⟨Witness.linear .positive case_50_33_13, case_50_33_13_checked⟩

    · exact ⟨Witness.linear .positive case_50_33_14, case_50_33_14_checked⟩

    · exact ⟨Witness.linear .positive case_50_33_15, case_50_33_15_checked⟩

    · exact ⟨Witness.linear .conditional case_50_33_16, case_50_33_16_checked⟩

    · exact ⟨Witness.linear .conditional case_50_33_17, case_50_33_17_checked⟩

    · exact ⟨Witness.linear .conditional case_50_33_18, case_50_33_18_checked⟩

    · exact ⟨Witness.linear .conditional case_50_33_19, case_50_33_19_checked⟩

    · exact ⟨Witness.linear .negative case_50_33_20, case_50_33_20_checked⟩

    · exact ⟨Witness.linear .negative case_50_33_21, case_50_33_21_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_50_34_1_checked⟩

    · exact ⟨Witness.rising, case_50_34_2_checked⟩

    · exact ⟨Witness.rising, case_50_34_3_checked⟩

    · exact ⟨Witness.rising, case_50_34_4_checked⟩

    · exact ⟨Witness.rising, case_50_34_5_checked⟩

    · exact ⟨Witness.rising, case_50_34_6_checked⟩

    · exact ⟨Witness.rising, case_50_34_7_checked⟩

    · exact ⟨Witness.rising, case_50_34_8_checked⟩

    · exact ⟨Witness.rising, case_50_34_9_checked⟩

    · exact ⟨Witness.linear .positive case_50_34_10, case_50_34_10_checked⟩

    · exact ⟨Witness.linear .positive case_50_34_11, case_50_34_11_checked⟩

    · exact ⟨Witness.linear .positive case_50_34_12, case_50_34_12_checked⟩

    · exact ⟨Witness.linear .positive case_50_34_13, case_50_34_13_checked⟩

    · exact ⟨Witness.linear .positive case_50_34_14, case_50_34_14_checked⟩

    · exact ⟨Witness.linear .positive case_50_34_15, case_50_34_15_checked⟩

    · exact ⟨Witness.linear .conditional case_50_34_16, case_50_34_16_checked⟩

    · exact ⟨Witness.linear .conditional case_50_34_17, case_50_34_17_checked⟩

    · exact ⟨Witness.linear .conditional case_50_34_18, case_50_34_18_checked⟩

    · exact ⟨Witness.linear .conditional case_50_34_19, case_50_34_19_checked⟩

    · exact ⟨Witness.linear .negative case_50_34_20, case_50_34_20_checked⟩

    · exact ⟨Witness.linear .negative case_50_34_21, case_50_34_21_checked⟩

    · exact ⟨Witness.linear .negative case_50_34_22, case_50_34_22_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_50_35_1_checked⟩

    · exact ⟨Witness.rising, case_50_35_2_checked⟩

    · exact ⟨Witness.rising, case_50_35_3_checked⟩

    · exact ⟨Witness.rising, case_50_35_4_checked⟩

    · exact ⟨Witness.rising, case_50_35_5_checked⟩

    · exact ⟨Witness.rising, case_50_35_6_checked⟩

    · exact ⟨Witness.rising, case_50_35_7_checked⟩

    · exact ⟨Witness.rising, case_50_35_8_checked⟩

    · exact ⟨Witness.rising, case_50_35_9_checked⟩

    · exact ⟨Witness.linear .positive case_50_35_10, case_50_35_10_checked⟩

    · exact ⟨Witness.linear .positive case_50_35_11, case_50_35_11_checked⟩

    · exact ⟨Witness.linear .positive case_50_35_12, case_50_35_12_checked⟩

    · exact ⟨Witness.linear .positive case_50_35_13, case_50_35_13_checked⟩

    · exact ⟨Witness.linear .positive case_50_35_14, case_50_35_14_checked⟩

    · exact ⟨Witness.linear .positive case_50_35_15, case_50_35_15_checked⟩

    · exact ⟨Witness.linear .positive case_50_35_16, case_50_35_16_checked⟩

    · exact ⟨Witness.linear .conditional case_50_35_17, case_50_35_17_checked⟩

    · exact ⟨Witness.linear .conditional case_50_35_18, case_50_35_18_checked⟩

    · exact ⟨Witness.linear .conditional case_50_35_19, case_50_35_19_checked⟩

    · exact ⟨Witness.linear .negative case_50_35_20, case_50_35_20_checked⟩

    · exact ⟨Witness.linear .negative case_50_35_21, case_50_35_21_checked⟩

    · exact ⟨Witness.linear .negative case_50_35_22, case_50_35_22_checked⟩

  · have hkHi : k ≤ 23 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_50_36_1_checked⟩

    · exact ⟨Witness.rising, case_50_36_2_checked⟩

    · exact ⟨Witness.rising, case_50_36_3_checked⟩

    · exact ⟨Witness.rising, case_50_36_4_checked⟩

    · exact ⟨Witness.rising, case_50_36_5_checked⟩

    · exact ⟨Witness.rising, case_50_36_6_checked⟩

    · exact ⟨Witness.rising, case_50_36_7_checked⟩

    · exact ⟨Witness.rising, case_50_36_8_checked⟩

    · exact ⟨Witness.rising, case_50_36_9_checked⟩

    · exact ⟨Witness.linear .positive case_50_36_10, case_50_36_10_checked⟩

    · exact ⟨Witness.linear .positive case_50_36_11, case_50_36_11_checked⟩

    · exact ⟨Witness.linear .positive case_50_36_12, case_50_36_12_checked⟩

    · exact ⟨Witness.linear .positive case_50_36_13, case_50_36_13_checked⟩

    · exact ⟨Witness.linear .positive case_50_36_14, case_50_36_14_checked⟩

    · exact ⟨Witness.linear .positive case_50_36_15, case_50_36_15_checked⟩

    · exact ⟨Witness.linear .positive case_50_36_16, case_50_36_16_checked⟩

    · exact ⟨Witness.linear .positive case_50_36_17, case_50_36_17_checked⟩

    · exact ⟨Witness.linear .conditional case_50_36_18, case_50_36_18_checked⟩

    · exact ⟨Witness.linear .conditional case_50_36_19, case_50_36_19_checked⟩

    · exact ⟨Witness.linear .conditional case_50_36_20, case_50_36_20_checked⟩

    · exact ⟨Witness.linear .negative case_50_36_21, case_50_36_21_checked⟩

    · exact ⟨Witness.linear .negative case_50_36_22, case_50_36_22_checked⟩

    · exact ⟨Witness.linear .negative case_50_36_23, case_50_36_23_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_50_37_1_checked⟩

    · exact ⟨Witness.rising, case_50_37_2_checked⟩

    · exact ⟨Witness.rising, case_50_37_3_checked⟩

    · exact ⟨Witness.rising, case_50_37_4_checked⟩

    · exact ⟨Witness.rising, case_50_37_5_checked⟩

    · exact ⟨Witness.rising, case_50_37_6_checked⟩

    · exact ⟨Witness.rising, case_50_37_7_checked⟩

    · exact ⟨Witness.rising, case_50_37_8_checked⟩

    · exact ⟨Witness.rising, case_50_37_9_checked⟩

    · exact ⟨Witness.linear .positive case_50_37_10, case_50_37_10_checked⟩

    · exact ⟨Witness.linear .positive case_50_37_11, case_50_37_11_checked⟩

    · exact ⟨Witness.linear .positive case_50_37_12, case_50_37_12_checked⟩

    · exact ⟨Witness.linear .positive case_50_37_13, case_50_37_13_checked⟩

    · exact ⟨Witness.linear .positive case_50_37_14, case_50_37_14_checked⟩

    · exact ⟨Witness.linear .positive case_50_37_15, case_50_37_15_checked⟩

    · exact ⟨Witness.linear .positive case_50_37_16, case_50_37_16_checked⟩

    · exact ⟨Witness.linear .positive case_50_37_17, case_50_37_17_checked⟩

    · exact ⟨Witness.linear .conditional case_50_37_18, case_50_37_18_checked⟩

    · exact ⟨Witness.linear .conditional case_50_37_19, case_50_37_19_checked⟩

    · exact ⟨Witness.linear .conditional case_50_37_20, case_50_37_20_checked⟩

    · exact ⟨Witness.linear .conditional case_50_37_21, case_50_37_21_checked⟩

    · exact ⟨Witness.linear .negative case_50_37_22, case_50_37_22_checked⟩

    · exact ⟨Witness.linear .negative case_50_37_23, case_50_37_23_checked⟩

    · exact ⟨Witness.linear .negative case_50_37_24, case_50_37_24_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_50_38_1_checked⟩

    · exact ⟨Witness.rising, case_50_38_2_checked⟩

    · exact ⟨Witness.rising, case_50_38_3_checked⟩

    · exact ⟨Witness.rising, case_50_38_4_checked⟩

    · exact ⟨Witness.rising, case_50_38_5_checked⟩

    · exact ⟨Witness.rising, case_50_38_6_checked⟩

    · exact ⟨Witness.rising, case_50_38_7_checked⟩

    · exact ⟨Witness.rising, case_50_38_8_checked⟩

    · exact ⟨Witness.rising, case_50_38_9_checked⟩

    · exact ⟨Witness.linear .positive case_50_38_10, case_50_38_10_checked⟩

    · exact ⟨Witness.linear .positive case_50_38_11, case_50_38_11_checked⟩

    · exact ⟨Witness.linear .positive case_50_38_12, case_50_38_12_checked⟩

    · exact ⟨Witness.linear .positive case_50_38_13, case_50_38_13_checked⟩

    · exact ⟨Witness.linear .positive case_50_38_14, case_50_38_14_checked⟩

    · exact ⟨Witness.linear .positive case_50_38_15, case_50_38_15_checked⟩

    · exact ⟨Witness.linear .positive case_50_38_16, case_50_38_16_checked⟩

    · exact ⟨Witness.linear .positive case_50_38_17, case_50_38_17_checked⟩

    · exact ⟨Witness.linear .positive case_50_38_18, case_50_38_18_checked⟩

    · exact ⟨Witness.linear .conditional case_50_38_19, case_50_38_19_checked⟩

    · exact ⟨Witness.linear .conditional case_50_38_20, case_50_38_20_checked⟩

    · exact ⟨Witness.linear .conditional case_50_38_21, case_50_38_21_checked⟩

    · exact ⟨Witness.linear .conditional case_50_38_22, case_50_38_22_checked⟩

    · exact ⟨Witness.linear .negative case_50_38_23, case_50_38_23_checked⟩

    · exact ⟨Witness.linear .negative case_50_38_24, case_50_38_24_checked⟩

  · have hkHi : k ≤ 25 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_50_39_1_checked⟩

    · exact ⟨Witness.rising, case_50_39_2_checked⟩

    · exact ⟨Witness.rising, case_50_39_3_checked⟩

    · exact ⟨Witness.rising, case_50_39_4_checked⟩

    · exact ⟨Witness.rising, case_50_39_5_checked⟩

    · exact ⟨Witness.rising, case_50_39_6_checked⟩

    · exact ⟨Witness.rising, case_50_39_7_checked⟩

    · exact ⟨Witness.rising, case_50_39_8_checked⟩

    · exact ⟨Witness.rising, case_50_39_9_checked⟩

    · exact ⟨Witness.linear .positive case_50_39_10, case_50_39_10_checked⟩

    · exact ⟨Witness.linear .positive case_50_39_11, case_50_39_11_checked⟩

    · exact ⟨Witness.linear .positive case_50_39_12, case_50_39_12_checked⟩

    · exact ⟨Witness.linear .positive case_50_39_13, case_50_39_13_checked⟩

    · exact ⟨Witness.linear .positive case_50_39_14, case_50_39_14_checked⟩

    · exact ⟨Witness.linear .positive case_50_39_15, case_50_39_15_checked⟩

    · exact ⟨Witness.linear .positive case_50_39_16, case_50_39_16_checked⟩

    · exact ⟨Witness.linear .positive case_50_39_17, case_50_39_17_checked⟩

    · exact ⟨Witness.linear .positive case_50_39_18, case_50_39_18_checked⟩

    · exact ⟨Witness.linear .positive case_50_39_19, case_50_39_19_checked⟩

    · exact ⟨Witness.linear .conditional case_50_39_20, case_50_39_20_checked⟩

    · exact ⟨Witness.linear .conditional case_50_39_21, case_50_39_21_checked⟩

    · exact ⟨Witness.linear .conditional case_50_39_22, case_50_39_22_checked⟩

    · exact ⟨Witness.linear .negative case_50_39_23, case_50_39_23_checked⟩

    · exact ⟨Witness.linear .negative case_50_39_24, case_50_39_24_checked⟩

    · exact ⟨Witness.linear .negative case_50_39_25, case_50_39_25_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_50_40_1_checked⟩

    · exact ⟨Witness.rising, case_50_40_2_checked⟩

    · exact ⟨Witness.rising, case_50_40_3_checked⟩

    · exact ⟨Witness.rising, case_50_40_4_checked⟩

    · exact ⟨Witness.rising, case_50_40_5_checked⟩

    · exact ⟨Witness.rising, case_50_40_6_checked⟩

    · exact ⟨Witness.rising, case_50_40_7_checked⟩

    · exact ⟨Witness.rising, case_50_40_8_checked⟩

    · exact ⟨Witness.rising, case_50_40_9_checked⟩

    · exact ⟨Witness.linear .positive case_50_40_10, case_50_40_10_checked⟩

    · exact ⟨Witness.linear .positive case_50_40_11, case_50_40_11_checked⟩

    · exact ⟨Witness.linear .positive case_50_40_12, case_50_40_12_checked⟩

    · exact ⟨Witness.linear .positive case_50_40_13, case_50_40_13_checked⟩

    · exact ⟨Witness.linear .positive case_50_40_14, case_50_40_14_checked⟩

    · exact ⟨Witness.linear .positive case_50_40_15, case_50_40_15_checked⟩

    · exact ⟨Witness.linear .positive case_50_40_16, case_50_40_16_checked⟩

    · exact ⟨Witness.linear .positive case_50_40_17, case_50_40_17_checked⟩

    · exact ⟨Witness.linear .positive case_50_40_18, case_50_40_18_checked⟩

    · exact ⟨Witness.linear .positive case_50_40_19, case_50_40_19_checked⟩

    · exact ⟨Witness.linear .conditional case_50_40_20, case_50_40_20_checked⟩

    · exact ⟨Witness.linear .conditional case_50_40_21, case_50_40_21_checked⟩

    · exact ⟨Witness.linear .conditional case_50_40_22, case_50_40_22_checked⟩

    · exact ⟨Witness.linear .negative case_50_40_23, case_50_40_23_checked⟩

    · exact ⟨Witness.linear .negative case_50_40_24, case_50_40_24_checked⟩

    · exact ⟨Witness.linear .negative case_50_40_25, case_50_40_25_checked⟩

    · exact ⟨Witness.linear .negative case_50_40_26, case_50_40_26_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_50_41_1_checked⟩

    · exact ⟨Witness.rising, case_50_41_2_checked⟩

    · exact ⟨Witness.rising, case_50_41_3_checked⟩

    · exact ⟨Witness.rising, case_50_41_4_checked⟩

    · exact ⟨Witness.rising, case_50_41_5_checked⟩

    · exact ⟨Witness.rising, case_50_41_6_checked⟩

    · exact ⟨Witness.rising, case_50_41_7_checked⟩

    · exact ⟨Witness.rising, case_50_41_8_checked⟩

    · exact ⟨Witness.rising, case_50_41_9_checked⟩

    · exact ⟨Witness.linear .positive case_50_41_10, case_50_41_10_checked⟩

    · exact ⟨Witness.linear .positive case_50_41_11, case_50_41_11_checked⟩

    · exact ⟨Witness.linear .positive case_50_41_12, case_50_41_12_checked⟩

    · exact ⟨Witness.linear .positive case_50_41_13, case_50_41_13_checked⟩

    · exact ⟨Witness.linear .positive case_50_41_14, case_50_41_14_checked⟩

    · exact ⟨Witness.linear .positive case_50_41_15, case_50_41_15_checked⟩

    · exact ⟨Witness.linear .positive case_50_41_16, case_50_41_16_checked⟩

    · exact ⟨Witness.linear .positive case_50_41_17, case_50_41_17_checked⟩

    · exact ⟨Witness.linear .positive case_50_41_18, case_50_41_18_checked⟩

    · exact ⟨Witness.linear .positive case_50_41_19, case_50_41_19_checked⟩

    · exact ⟨Witness.linear .positive case_50_41_20, case_50_41_20_checked⟩

    · exact ⟨Witness.linear .conditional case_50_41_21, case_50_41_21_checked⟩

    · exact ⟨Witness.linear .conditional case_50_41_22, case_50_41_22_checked⟩

    · exact ⟨Witness.linear .negative case_50_41_23, case_50_41_23_checked⟩

    · exact ⟨Witness.linear .negative case_50_41_24, case_50_41_24_checked⟩

    · exact ⟨Witness.linear .negative case_50_41_25, case_50_41_25_checked⟩

    · exact ⟨Witness.linear .negative case_50_41_26, case_50_41_26_checked⟩

  · have hkHi : k ≤ 27 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_50_42_1_checked⟩

    · exact ⟨Witness.rising, case_50_42_2_checked⟩

    · exact ⟨Witness.rising, case_50_42_3_checked⟩

    · exact ⟨Witness.rising, case_50_42_4_checked⟩

    · exact ⟨Witness.rising, case_50_42_5_checked⟩

    · exact ⟨Witness.rising, case_50_42_6_checked⟩

    · exact ⟨Witness.rising, case_50_42_7_checked⟩

    · exact ⟨Witness.rising, case_50_42_8_checked⟩

    · exact ⟨Witness.rising, case_50_42_9_checked⟩

    · exact ⟨Witness.linear .positive case_50_42_10, case_50_42_10_checked⟩

    · exact ⟨Witness.linear .positive case_50_42_11, case_50_42_11_checked⟩

    · exact ⟨Witness.linear .positive case_50_42_12, case_50_42_12_checked⟩

    · exact ⟨Witness.linear .positive case_50_42_13, case_50_42_13_checked⟩

    · exact ⟨Witness.linear .positive case_50_42_14, case_50_42_14_checked⟩

    · exact ⟨Witness.linear .positive case_50_42_15, case_50_42_15_checked⟩

    · exact ⟨Witness.linear .positive case_50_42_16, case_50_42_16_checked⟩

    · exact ⟨Witness.linear .positive case_50_42_17, case_50_42_17_checked⟩

    · exact ⟨Witness.linear .positive case_50_42_18, case_50_42_18_checked⟩

    · exact ⟨Witness.linear .positive case_50_42_19, case_50_42_19_checked⟩

    · exact ⟨Witness.linear .positive case_50_42_20, case_50_42_20_checked⟩

    · exact ⟨Witness.linear .conditional case_50_42_21, case_50_42_21_checked⟩

    · exact ⟨Witness.linear .conditional case_50_42_22, case_50_42_22_checked⟩

    · exact ⟨Witness.linear .negative case_50_42_23, case_50_42_23_checked⟩

    · exact ⟨Witness.linear .negative case_50_42_24, case_50_42_24_checked⟩

    · exact ⟨Witness.linear .negative case_50_42_25, case_50_42_25_checked⟩

    · exact ⟨Witness.linear .negative case_50_42_26, case_50_42_26_checked⟩

    · exact ⟨Witness.linear .negative case_50_42_27, case_50_42_27_checked⟩

  · have hkHi : k ≤ 28 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_50_43_1_checked⟩

    · exact ⟨Witness.rising, case_50_43_2_checked⟩

    · exact ⟨Witness.rising, case_50_43_3_checked⟩

    · exact ⟨Witness.rising, case_50_43_4_checked⟩

    · exact ⟨Witness.rising, case_50_43_5_checked⟩

    · exact ⟨Witness.rising, case_50_43_6_checked⟩

    · exact ⟨Witness.rising, case_50_43_7_checked⟩

    · exact ⟨Witness.rising, case_50_43_8_checked⟩

    · exact ⟨Witness.linear .positive case_50_43_9, case_50_43_9_checked⟩

    · exact ⟨Witness.linear .positive case_50_43_10, case_50_43_10_checked⟩

    · exact ⟨Witness.linear .positive case_50_43_11, case_50_43_11_checked⟩

    · exact ⟨Witness.linear .positive case_50_43_12, case_50_43_12_checked⟩

    · exact ⟨Witness.linear .positive case_50_43_13, case_50_43_13_checked⟩

    · exact ⟨Witness.linear .positive case_50_43_14, case_50_43_14_checked⟩

    · exact ⟨Witness.linear .positive case_50_43_15, case_50_43_15_checked⟩

    · exact ⟨Witness.linear .positive case_50_43_16, case_50_43_16_checked⟩

    · exact ⟨Witness.linear .positive case_50_43_17, case_50_43_17_checked⟩

    · exact ⟨Witness.linear .positive case_50_43_18, case_50_43_18_checked⟩

    · exact ⟨Witness.linear .positive case_50_43_19, case_50_43_19_checked⟩

    · exact ⟨Witness.linear .positive case_50_43_20, case_50_43_20_checked⟩

    · exact ⟨Witness.linear .positive case_50_43_21, case_50_43_21_checked⟩

    · exact ⟨Witness.linear .conditional case_50_43_22, case_50_43_22_checked⟩

    · exact ⟨Witness.linear .negative case_50_43_23, case_50_43_23_checked⟩

    · exact ⟨Witness.linear .negative case_50_43_24, case_50_43_24_checked⟩

    · exact ⟨Witness.linear .negative case_50_43_25, case_50_43_25_checked⟩

    · exact ⟨Witness.linear .negative case_50_43_26, case_50_43_26_checked⟩

    · exact ⟨Witness.linear .negative case_50_43_27, case_50_43_27_checked⟩

    · exact ⟨Witness.linear .negative case_50_43_28, case_50_43_28_checked⟩

  · have hkHi : k ≤ 28 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_50_44_1_checked⟩

    · exact ⟨Witness.rising, case_50_44_2_checked⟩

    · exact ⟨Witness.rising, case_50_44_3_checked⟩

    · exact ⟨Witness.rising, case_50_44_4_checked⟩

    · exact ⟨Witness.rising, case_50_44_5_checked⟩

    · exact ⟨Witness.rising, case_50_44_6_checked⟩

    · exact ⟨Witness.rising, case_50_44_7_checked⟩

    · exact ⟨Witness.rising, case_50_44_8_checked⟩

    · exact ⟨Witness.linear .positive case_50_44_9, case_50_44_9_checked⟩

    · exact ⟨Witness.linear .positive case_50_44_10, case_50_44_10_checked⟩

    · exact ⟨Witness.linear .positive case_50_44_11, case_50_44_11_checked⟩

    · exact ⟨Witness.linear .positive case_50_44_12, case_50_44_12_checked⟩

    · exact ⟨Witness.linear .positive case_50_44_13, case_50_44_13_checked⟩

    · exact ⟨Witness.linear .positive case_50_44_14, case_50_44_14_checked⟩

    · exact ⟨Witness.linear .positive case_50_44_15, case_50_44_15_checked⟩

    · exact ⟨Witness.linear .positive case_50_44_16, case_50_44_16_checked⟩

    · exact ⟨Witness.linear .positive case_50_44_17, case_50_44_17_checked⟩

    · exact ⟨Witness.linear .positive case_50_44_18, case_50_44_18_checked⟩

    · exact ⟨Witness.linear .positive case_50_44_19, case_50_44_19_checked⟩

    · exact ⟨Witness.linear .positive case_50_44_20, case_50_44_20_checked⟩

    · exact ⟨Witness.linear .positive case_50_44_21, case_50_44_21_checked⟩

    · exact ⟨Witness.linear .positive case_50_44_22, case_50_44_22_checked⟩

    · exact ⟨Witness.linear .negative case_50_44_23, case_50_44_23_checked⟩

    · exact ⟨Witness.linear .negative case_50_44_24, case_50_44_24_checked⟩

    · exact ⟨Witness.linear .negative case_50_44_25, case_50_44_25_checked⟩

    · exact ⟨Witness.linear .negative case_50_44_26, case_50_44_26_checked⟩

    · exact ⟨Witness.linear .negative case_50_44_27, case_50_44_27_checked⟩

    · exact ⟨Witness.linear .negative case_50_44_28, case_50_44_28_checked⟩

  · have hkHi : k ≤ 29 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_50_45_1_checked⟩

    · exact ⟨Witness.rising, case_50_45_2_checked⟩

    · exact ⟨Witness.rising, case_50_45_3_checked⟩

    · exact ⟨Witness.rising, case_50_45_4_checked⟩

    · exact ⟨Witness.rising, case_50_45_5_checked⟩

    · exact ⟨Witness.rising, case_50_45_6_checked⟩

    · exact ⟨Witness.rising, case_50_45_7_checked⟩

    · exact ⟨Witness.rising, case_50_45_8_checked⟩

    · exact ⟨Witness.linear .positive case_50_45_9, case_50_45_9_checked⟩

    · exact ⟨Witness.linear .positive case_50_45_10, case_50_45_10_checked⟩

    · exact ⟨Witness.linear .positive case_50_45_11, case_50_45_11_checked⟩

    · exact ⟨Witness.linear .positive case_50_45_12, case_50_45_12_checked⟩

    · exact ⟨Witness.linear .positive case_50_45_13, case_50_45_13_checked⟩

    · exact ⟨Witness.linear .positive case_50_45_14, case_50_45_14_checked⟩

    · exact ⟨Witness.linear .positive case_50_45_15, case_50_45_15_checked⟩

    · exact ⟨Witness.linear .positive case_50_45_16, case_50_45_16_checked⟩

    · exact ⟨Witness.linear .positive case_50_45_17, case_50_45_17_checked⟩

    · exact ⟨Witness.linear .positive case_50_45_18, case_50_45_18_checked⟩

    · exact ⟨Witness.linear .positive case_50_45_19, case_50_45_19_checked⟩

    · exact ⟨Witness.linear .positive case_50_45_20, case_50_45_20_checked⟩

    · exact ⟨Witness.linear .positive case_50_45_21, case_50_45_21_checked⟩

    · exact ⟨Witness.linear .positive case_50_45_22, case_50_45_22_checked⟩

    · exact ⟨Witness.linear .conditional case_50_45_23, case_50_45_23_checked⟩

    · exact ⟨Witness.linear .negative case_50_45_24, case_50_45_24_checked⟩

    · exact ⟨Witness.linear .negative case_50_45_25, case_50_45_25_checked⟩

    · exact ⟨Witness.linear .negative case_50_45_26, case_50_45_26_checked⟩

    · exact ⟨Witness.linear .negative case_50_45_27, case_50_45_27_checked⟩

    · exact ⟨Witness.linear .negative case_50_45_28, case_50_45_28_checked⟩

    · exact ⟨Witness.linear .negative case_50_45_29, case_50_45_29_checked⟩

  · have hkHi : k ≤ 30 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_50_46_1_checked⟩

    · exact ⟨Witness.rising, case_50_46_2_checked⟩

    · exact ⟨Witness.rising, case_50_46_3_checked⟩

    · exact ⟨Witness.rising, case_50_46_4_checked⟩

    · exact ⟨Witness.rising, case_50_46_5_checked⟩

    · exact ⟨Witness.rising, case_50_46_6_checked⟩

    · exact ⟨Witness.rising, case_50_46_7_checked⟩

    · exact ⟨Witness.rising, case_50_46_8_checked⟩

    · exact ⟨Witness.linear .positive case_50_46_9, case_50_46_9_checked⟩

    · exact ⟨Witness.linear .positive case_50_46_10, case_50_46_10_checked⟩

    · exact ⟨Witness.linear .positive case_50_46_11, case_50_46_11_checked⟩

    · exact ⟨Witness.linear .positive case_50_46_12, case_50_46_12_checked⟩

    · exact ⟨Witness.linear .positive case_50_46_13, case_50_46_13_checked⟩

    · exact ⟨Witness.linear .positive case_50_46_14, case_50_46_14_checked⟩

    · exact ⟨Witness.linear .positive case_50_46_15, case_50_46_15_checked⟩

    · exact ⟨Witness.linear .positive case_50_46_16, case_50_46_16_checked⟩

    · exact ⟨Witness.linear .positive case_50_46_17, case_50_46_17_checked⟩

    · exact ⟨Witness.linear .positive case_50_46_18, case_50_46_18_checked⟩

    · exact ⟨Witness.linear .positive case_50_46_19, case_50_46_19_checked⟩

    · exact ⟨Witness.linear .positive case_50_46_20, case_50_46_20_checked⟩

    · exact ⟨Witness.linear .positive case_50_46_21, case_50_46_21_checked⟩

    · exact ⟨Witness.linear .positive case_50_46_22, case_50_46_22_checked⟩

    · exact ⟨Witness.linear .positive case_50_46_23, case_50_46_23_checked⟩

    · exact ⟨Witness.linear .negative case_50_46_24, case_50_46_24_checked⟩

    · exact ⟨Witness.linear .negative case_50_46_25, case_50_46_25_checked⟩

    · exact ⟨Witness.linear .negative case_50_46_26, case_50_46_26_checked⟩

    · exact ⟨Witness.linear .negative case_50_46_27, case_50_46_27_checked⟩

    · exact ⟨Witness.linear .negative case_50_46_28, case_50_46_28_checked⟩

    · exact ⟨Witness.linear .negative case_50_46_29, case_50_46_29_checked⟩

    · exact ⟨Witness.linear .negative case_50_46_30, case_50_46_30_checked⟩

  · have hkHi : k ≤ 30 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_50_47_1_checked⟩

    · exact ⟨Witness.rising, case_50_47_2_checked⟩

    · exact ⟨Witness.rising, case_50_47_3_checked⟩

    · exact ⟨Witness.rising, case_50_47_4_checked⟩

    · exact ⟨Witness.rising, case_50_47_5_checked⟩

    · exact ⟨Witness.rising, case_50_47_6_checked⟩

    · exact ⟨Witness.rising, case_50_47_7_checked⟩

    · exact ⟨Witness.rising, case_50_47_8_checked⟩

    · exact ⟨Witness.linear .positive case_50_47_9, case_50_47_9_checked⟩

    · exact ⟨Witness.linear .positive case_50_47_10, case_50_47_10_checked⟩

    · exact ⟨Witness.linear .positive case_50_47_11, case_50_47_11_checked⟩

    · exact ⟨Witness.linear .positive case_50_47_12, case_50_47_12_checked⟩

    · exact ⟨Witness.linear .positive case_50_47_13, case_50_47_13_checked⟩

    · exact ⟨Witness.linear .positive case_50_47_14, case_50_47_14_checked⟩

    · exact ⟨Witness.linear .positive case_50_47_15, case_50_47_15_checked⟩

    · exact ⟨Witness.linear .positive case_50_47_16, case_50_47_16_checked⟩

    · exact ⟨Witness.linear .positive case_50_47_17, case_50_47_17_checked⟩

    · exact ⟨Witness.linear .positive case_50_47_18, case_50_47_18_checked⟩

    · exact ⟨Witness.linear .positive case_50_47_19, case_50_47_19_checked⟩

    · exact ⟨Witness.linear .positive case_50_47_20, case_50_47_20_checked⟩

    · exact ⟨Witness.linear .positive case_50_47_21, case_50_47_21_checked⟩

    · exact ⟨Witness.linear .positive case_50_47_22, case_50_47_22_checked⟩

    · exact ⟨Witness.linear .positive case_50_47_23, case_50_47_23_checked⟩

    · exact ⟨Witness.linear .negative case_50_47_24, case_50_47_24_checked⟩

    · exact ⟨Witness.linear .negative case_50_47_25, case_50_47_25_checked⟩

    · exact ⟨Witness.linear .negative case_50_47_26, case_50_47_26_checked⟩

    · exact ⟨Witness.linear .negative case_50_47_27, case_50_47_27_checked⟩

    · exact ⟨Witness.linear .negative case_50_47_28, case_50_47_28_checked⟩

    · exact ⟨Witness.linear .negative case_50_47_29, case_50_47_29_checked⟩

    · exact ⟨Witness.linear .negative case_50_47_30, case_50_47_30_checked⟩

  · have hkHi : k ≤ 31 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_50_48_1_checked⟩

    · exact ⟨Witness.rising, case_50_48_2_checked⟩

    · exact ⟨Witness.rising, case_50_48_3_checked⟩

    · exact ⟨Witness.rising, case_50_48_4_checked⟩

    · exact ⟨Witness.rising, case_50_48_5_checked⟩

    · exact ⟨Witness.rising, case_50_48_6_checked⟩

    · exact ⟨Witness.rising, case_50_48_7_checked⟩

    · exact ⟨Witness.rising, case_50_48_8_checked⟩

    · exact ⟨Witness.linear .positive case_50_48_9, case_50_48_9_checked⟩

    · exact ⟨Witness.linear .positive case_50_48_10, case_50_48_10_checked⟩

    · exact ⟨Witness.linear .positive case_50_48_11, case_50_48_11_checked⟩

    · exact ⟨Witness.linear .positive case_50_48_12, case_50_48_12_checked⟩

    · exact ⟨Witness.linear .positive case_50_48_13, case_50_48_13_checked⟩

    · exact ⟨Witness.linear .positive case_50_48_14, case_50_48_14_checked⟩

    · exact ⟨Witness.linear .positive case_50_48_15, case_50_48_15_checked⟩

    · exact ⟨Witness.linear .positive case_50_48_16, case_50_48_16_checked⟩

    · exact ⟨Witness.linear .positive case_50_48_17, case_50_48_17_checked⟩

    · exact ⟨Witness.linear .positive case_50_48_18, case_50_48_18_checked⟩

    · exact ⟨Witness.linear .positive case_50_48_19, case_50_48_19_checked⟩

    · exact ⟨Witness.linear .positive case_50_48_20, case_50_48_20_checked⟩

    · exact ⟨Witness.linear .positive case_50_48_21, case_50_48_21_checked⟩

    · exact ⟨Witness.linear .positive case_50_48_22, case_50_48_22_checked⟩

    · exact ⟨Witness.linear .positive case_50_48_23, case_50_48_23_checked⟩

    · exact ⟨Witness.linear .positive case_50_48_24, case_50_48_24_checked⟩

    · exact ⟨Witness.linear .negative case_50_48_25, case_50_48_25_checked⟩

    · exact ⟨Witness.linear .negative case_50_48_26, case_50_48_26_checked⟩

    · exact ⟨Witness.linear .negative case_50_48_27, case_50_48_27_checked⟩

    · exact ⟨Witness.linear .negative case_50_48_28, case_50_48_28_checked⟩

    · exact ⟨Witness.linear .negative case_50_48_29, case_50_48_29_checked⟩

    · exact ⟨Witness.linear .negative case_50_48_30, case_50_48_30_checked⟩

    · exact ⟨Witness.linear .negative case_50_48_31, case_50_48_31_checked⟩

  · have hkHi : k ≤ 32 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_50_49_1_checked⟩

    · exact ⟨Witness.rising, case_50_49_2_checked⟩

    · exact ⟨Witness.rising, case_50_49_3_checked⟩

    · exact ⟨Witness.rising, case_50_49_4_checked⟩

    · exact ⟨Witness.rising, case_50_49_5_checked⟩

    · exact ⟨Witness.rising, case_50_49_6_checked⟩

    · exact ⟨Witness.rising, case_50_49_7_checked⟩

    · exact ⟨Witness.rising, case_50_49_8_checked⟩

    · exact ⟨Witness.linear .positive case_50_49_9, case_50_49_9_checked⟩

    · exact ⟨Witness.linear .positive case_50_49_10, case_50_49_10_checked⟩

    · exact ⟨Witness.linear .positive case_50_49_11, case_50_49_11_checked⟩

    · exact ⟨Witness.linear .positive case_50_49_12, case_50_49_12_checked⟩

    · exact ⟨Witness.linear .positive case_50_49_13, case_50_49_13_checked⟩

    · exact ⟨Witness.linear .positive case_50_49_14, case_50_49_14_checked⟩

    · exact ⟨Witness.linear .positive case_50_49_15, case_50_49_15_checked⟩

    · exact ⟨Witness.linear .positive case_50_49_16, case_50_49_16_checked⟩

    · exact ⟨Witness.linear .positive case_50_49_17, case_50_49_17_checked⟩

    · exact ⟨Witness.linear .positive case_50_49_18, case_50_49_18_checked⟩

    · exact ⟨Witness.linear .positive case_50_49_19, case_50_49_19_checked⟩

    · exact ⟨Witness.linear .positive case_50_49_20, case_50_49_20_checked⟩

    · exact ⟨Witness.linear .positive case_50_49_21, case_50_49_21_checked⟩

    · exact ⟨Witness.linear .positive case_50_49_22, case_50_49_22_checked⟩

    · exact ⟨Witness.linear .positive case_50_49_23, case_50_49_23_checked⟩

    · exact ⟨Witness.linear .positive case_50_49_24, case_50_49_24_checked⟩

    · exact ⟨Witness.linear .negative case_50_49_25, case_50_49_25_checked⟩

    · exact ⟨Witness.linear .negative case_50_49_26, case_50_49_26_checked⟩

    · exact ⟨Witness.linear .negative case_50_49_27, case_50_49_27_checked⟩

    · exact ⟨Witness.linear .negative case_50_49_28, case_50_49_28_checked⟩

    · exact ⟨Witness.linear .negative case_50_49_29, case_50_49_29_checked⟩

    · exact ⟨Witness.linear .negative case_50_49_30, case_50_49_30_checked⟩

    · exact ⟨Witness.linear .negative case_50_49_31, case_50_49_31_checked⟩

    · exact ⟨Witness.linear .negative case_50_49_32, case_50_49_32_checked⟩


#print axioms coverage_50
end ForestUnimodality.FiniteRows.FiniteData
