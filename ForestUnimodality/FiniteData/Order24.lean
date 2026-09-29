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

theorem case_24_12_1_checked :
    (Witness.rising).check 24 12 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_12_2_checked :
    (Witness.rising).check 24 12 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_12_3_checked :
    (Witness.rising).check 24 12 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_12_4_checked :
    (Witness.rising).check 24 12 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_12_5_checked :
    (Witness.rising).check 24 12 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_12_6_checked :
    (Witness.rising).check 24 12 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_12_7 : Certificate := {
  objectiveScale := 1200000
  eta := 2079000
  rows := #[⟨.count 2, 16405200⟩, ⟨.count 3, 9986760⟩, ⟨.count 4, 2876160⟩, ⟨.count 5, 1199100⟩, ⟨.count 6, 1200600⟩, ⟨.path 8, 475536⟩, ⟨.privateRow 8 0, 95088⟩, ⟨.hall 1 1, 100800⟩, ⟨.hall 6 1, 67320⟩, ⟨.hall 6 2, 17130⟩, ⟨.hall 0 3, 2041200⟩, ⟨.hall 1 3, 129465⟩, ⟨.hall 5 3, 18735⟩, ⟨.hall 4 5, 20200⟩, ⟨.hall 5 6, 122100⟩, ⟨.hall 3 8, 52080⟩]
  caps := #[0, 31680, 0, 0, 0, 1260, 0, 0, 96, 0, 0, 0, 0] }

theorem case_24_12_7_checked :
    (Witness.linear .positive case_24_12_7).check 24 12 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_13_1_checked :
    (Witness.rising).check 24 13 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_13_2_checked :
    (Witness.rising).check 24 13 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_13_3_checked :
    (Witness.rising).check 24 13 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_13_4_checked :
    (Witness.rising).check 24 13 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_13_5_checked :
    (Witness.rising).check 24 13 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_13_6_checked :
    (Witness.rising).check 24 13 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_13_7 : Certificate := {
  objectiveScale := 367500
  eta := 48527640
  rows := #[⟨.count 2, 10287648⟩, ⟨.count 3, 2571912⟩, ⟨.count 4, 857304⟩, ⟨.count 5, 367920⟩, ⟨.count 6, 367920⟩, ⟨.path 8, 122500⟩, ⟨.privateRow 7 0, 11592⟩, ⟨.privateRow 8 0, 20433⟩, ⟨.hall 5 3, 4068⟩, ⟨.hall 6 3, 3204⟩, ⟨.hall 4 6, 12152⟩]
  caps := #[0, 0, 2352, 588, 196, 0, 0, 476, 0, 0, 0, 0] }

theorem case_24_13_7_checked :
    (Witness.linear .positive case_24_13_7).check 24 13 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_13_8 : Certificate := {
  objectiveScale := 2965200000
  eta := 280246982400
  rows := #[⟨.count 2, 77576748480⟩, ⟨.count 3, 23993212320⟩, ⟨.count 4, 9185003520⟩, ⟨.count 5, 4049192400⟩, ⟨.count 6, 2828377200⟩, ⟨.count 7, 1676524080⟩, ⟨.count 9, 2974688640⟩, ⟨.path 6, 1186054100⟩, ⟨.privateRow 4 6, 63195825⟩, ⟨.privateRow 5 4, 122640672⟩, ⟨.privateRow 5 5, 1175151120⟩, ⟨.privateRow 6 2, 37276800⟩, ⟨.privateRow 6 3, 835155640⟩, ⟨.privateRow 6 4, 692727200⟩, ⟨.privateRow 7 1, 627182160⟩, ⟨.privateRow 8 0, 248434340⟩, ⟨.hall 3 8, 1064625408⟩, ⟨.hall 4 8, 4322866240⟩, ⟨.hall 2 10, 7052431680⟩, ⟨.assumptionRow 8, 1677921960⟩]
  caps := #[0, 0, 9190440, 3415440, 0, 837760, 0, 4532520, 0, 0, 0, 0] }

theorem case_24_13_8_checked :
    (Witness.linear .conditional case_24_13_8).check 24 13 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_14_1_checked :
    (Witness.rising).check 24 14 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_14_2_checked :
    (Witness.rising).check 24 14 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_14_3_checked :
    (Witness.rising).check 24 14 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_14_4_checked :
    (Witness.rising).check 24 14 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_14_5_checked :
    (Witness.rising).check 24 14 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_14_6 : Certificate := {
  objectiveScale := 2026836000
  eta := 331217431776
  rows := #[⟨.count 2, 60821294688⟩, ⟨.count 3, 13020394464⟩, ⟨.count 4, 3478050576⟩, ⟨.count 5, 2027801160⟩, ⟨.path 6, 1158141600⟩, ⟨.privateRow 7 0, 41405364⟩, ⟨.hall 6 2, 1023759⟩, ⟨.hall 7 3, 21233520⟩, ⟨.hall 5 6, 31007680⟩]
  caps := #[0, 0, 0, 8257536, 0, 0, 413796, 8758827, 0, 0, 0] }

theorem case_24_14_6_checked :
    (Witness.linear .positive case_24_14_6).check 24 14 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_14_7 : Certificate := {
  objectiveScale := 98000
  eta := 21014532
  rows := #[⟨.count 2, 5144216⟩, ⟨.count 3, 1285515⟩, ⟨.count 4, 367752⟩, ⟨.count 5, 134750⟩, ⟨.count 6, 97944⟩, ⟨.path 7, 36750⟩, ⟨.hall 4 6, 3938⟩]
  caps := #[0, 6468, 784, 735, 168, 0, 56, 0, 0, 0, 0] }

theorem case_24_14_7_checked :
    (Witness.linear .positive case_24_14_7).check 24 14 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_14_8 : Certificate := {
  objectiveScale := 14220981500000
  eta := 3338419776587280
  rows := #[⟨.count 2, 776656719891360⟩, ⟨.count 3, 215612548690770⟩, ⟨.count 4, 65796499525680⟩, ⟨.count 5, 24488530143000⟩, ⟨.count 6, 14263075605240⟩, ⟨.count 7, 7024027182480⟩, ⟨.count 9, 13546338137640⟩, ⟨.path 5, 6520230070200⟩, ⟨.path 6, 3711564780000⟩, ⟨.privateRow 3 9, 6341135650850⟩, ⟨.privateRow 4 7, 11691779940225⟩, ⟨.privateRow 4 8, 17392829213760⟩, ⟨.privateRow 5 4, 27873123740⟩, ⟨.privateRow 5 5, 9592336441380⟩, ⟨.privateRow 5 6, 10849613415795⟩, ⟨.privateRow 6 3, 6886652501190⟩, ⟨.privateRow 6 4, 2542028885088⟩, ⟨.privateRow 7 1, 3596486221350⟩, ⟨.privateRow 8 0, 1236372131610⟩, ⟨.hall 3 10, 13363895873160⟩, ⟨.hall 2 11, 52011248898840⟩, ⟨.assumptionRow 8, 10564710272424⟩]
  caps := #[0, 0, 0, 66948077812, 63576793875, 19539759624, 13199447184, 0, 0, 674643362360, 0] }

theorem case_24_14_8_checked :
    (Witness.linear .conditional case_24_14_8).check 24 14 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_15_1_checked :
    (Witness.rising).check 24 15 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_15_2_checked :
    (Witness.rising).check 24 15 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_15_3_checked :
    (Witness.rising).check 24 15 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_15_4_checked :
    (Witness.rising).check 24 15 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_15_5_checked :
    (Witness.rising).check 24 15 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_15_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_24_15_6_checked :
    (Witness.linear .positive case_24_15_6).check 24 15 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_15_7 : Certificate := {
  objectiveScale := 1
  eta := 78
  rows := #[⟨.assumptionRow 7, 3⟩]
  caps := #[0, 0, 28, 11, 5, 3, 3, 4, 1, 0] }

theorem case_24_15_7_checked :
    (Witness.linear .conditional case_24_15_7).check 24 15 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_15_8 : Certificate := {
  objectiveScale := 19446000000
  eta := 7877216793600
  rows := #[⟨.count 2, 1666541646000⟩, ⟨.count 3, 435469834800⟩, ⟨.count 4, 120899671200⟩, ⟨.count 5, 39273141600⟩, ⟨.count 6, 13091047200⟩, ⟨.count 7, 4492026000⟩, ⟨.path 5, 22687156800⟩, ⟨.privateRow 2 13, 75016834200⟩, ⟨.privateRow 3 10, 69990043200⟩, ⟨.privateRow 3 11, 62246646000⟩, ⟨.privateRow 4 7, 18905012280⟩, ⟨.privateRow 4 8, 46428297300⟩, ⟨.privateRow 4 9, 18673993800⟩, ⟨.privateRow 5 4, 520708320⟩, ⟨.privateRow 5 5, 21946755600⟩, ⟨.privateRow 5 6, 17885964096⟩, ⟨.privateRow 6 2, 1123006500⟩, ⟨.privateRow 6 3, 15437901600⟩, ⟨.privateRow 7 1, 6048192150⟩, ⟨.privateRow 8 0, 2077562025⟩, ⟨.privateRow 9 0, 2566872000⟩, ⟨.assumptionRow 8, 16522618000⟩]
  caps := #[0, 2224714800, 9193800, 181473600, 56627340, 192268464, 62551300, 0, 0, 1477896000] }

theorem case_24_15_8_checked :
    (Witness.linear .conditional case_24_15_8).check 24 15 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_15_9 : Certificate := {
  objectiveScale := 18228000000
  eta := 14863898649600
  rows := #[⟨.count 2, 2633712681600⟩, ⟨.count 3, 467513046000⟩, ⟨.count 4, 69261192000⟩, ⟨.path 3, 70365335040⟩, ⟨.path 4, 69232756320⟩, ⟨.privateRow 2 13, 188066478600⟩, ⟨.privateRow 3 9, 25917091200⟩, ⟨.privateRow 3 10, 99460561200⟩, ⟨.privateRow 3 11, 97915217400⟩, ⟨.privateRow 4 6, 3649245600⟩, ⟨.privateRow 4 7, 35982306360⟩, ⟨.privateRow 4 8, 59109400350⟩, ⟨.privateRow 4 9, 40141701600⟩, ⟨.privateRow 5 4, 5834537280⟩, ⟨.privateRow 5 5, 25328743440⟩, ⟨.privateRow 5 6, 34156938816⟩, ⟨.privateRow 6 2, 4377698325⟩, ⟨.privateRow 6 3, 18679775400⟩, ⟨.privateRow 6 4, 5334228900⟩, ⟨.privateRow 7 0, 4381577200⟩, ⟨.privateRow 7 1, 6716659950⟩, ⟨.privateRow 8 0, 4691887200⟩, ⟨.privateRow 9 0, 1787385600⟩, ⟨.hall 2 12, 10827432000⟩]
  caps := #[0, 0, 0, 29628480, 0, 13440360, 324609525, 0, 266128800, 0] }

theorem case_24_15_9_checked :
    (Witness.linear .negative case_24_15_9).check 24 15 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_16_1_checked :
    (Witness.rising).check 24 16 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_16_2_checked :
    (Witness.rising).check 24 16 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_16_3_checked :
    (Witness.rising).check 24 16 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_16_4_checked :
    (Witness.rising).check 24 16 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_16_5_checked :
    (Witness.rising).check 24 16 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_16_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1, 1, 0, 0, 0] }

theorem case_24_16_6_checked :
    (Witness.linear .positive case_24_16_6).check 24 16 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_16_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0, 0] }

theorem case_24_16_7_checked :
    (Witness.linear .positive case_24_16_7).check 24 16 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_16_8 : Certificate := {
  objectiveScale := 5
  eta := 435
  rows := #[⟨.assumptionRow 8, 9⟩]
  caps := #[0, 0, 152, 56, 25, 13, 60, 63, 26] }

theorem case_24_16_8_checked :
    (Witness.linear .conditional case_24_16_8).check 24 16 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_16_9 : Certificate := {
  objectiveScale := 24
  eta := 585
  rows := #[⟨.assumptionRow 9, 19⟩]
  caps := #[0, 0, 264, 122, 52, 33, 735, 639, 347] }

theorem case_24_16_9_checked :
    (Witness.linear .conditional case_24_16_9).check 24 16 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_16_10 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 42, 42, 28] }

theorem case_24_16_10_checked :
    (Witness.linear .negative case_24_16_10).check 24 16 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_17_1_checked :
    (Witness.rising).check 24 17 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_17_2_checked :
    (Witness.rising).check 24 17 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_17_3_checked :
    (Witness.rising).check 24 17 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_17_4_checked :
    (Witness.rising).check 24 17 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_17_5_checked :
    (Witness.rising).check 24 17 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_17_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1, 1, 0, 0] }

theorem case_24_17_6_checked :
    (Witness.linear .positive case_24_17_6).check 24 17 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_17_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0] }

theorem case_24_17_7_checked :
    (Witness.linear .positive case_24_17_7).check 24 17 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_17_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1] }

theorem case_24_17_8_checked :
    (Witness.linear .positive case_24_17_8).check 24 17 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_17_9 : Certificate := {
  objectiveScale := 139
  eta := 9295
  rows := #[⟨.assumptionRow 9, 149⟩]
  caps := #[0, 0, 3399, 1392, 646, 308, 6545, 5210] }

theorem case_24_17_9_checked :
    (Witness.linear .conditional case_24_17_9).check 24 17 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_17_10 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 132, 132, 90] }

theorem case_24_17_10_checked :
    (Witness.linear .negative case_24_17_10).check 24 17 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_18_1_checked :
    (Witness.rising).check 24 18 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_18_2_checked :
    (Witness.rising).check 24 18 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_18_3_checked :
    (Witness.rising).check 24 18 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_18_4_checked :
    (Witness.rising).check 24 18 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_18_5_checked :
    (Witness.rising).check 24 18 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_18_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1, 1, 0] }

theorem case_24_18_6_checked :
    (Witness.linear .positive case_24_18_6).check 24 18 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_18_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1] }

theorem case_24_18_7_checked :
    (Witness.linear .positive case_24_18_7).check 24 18 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_18_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1] }

theorem case_24_18_8_checked :
    (Witness.linear .positive case_24_18_8).check 24 18 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_18_9 : Certificate := {
  objectiveScale := 4
  eta := 1573
  rows := #[⟨.assumptionRow 9, 9⟩]
  caps := #[0, 0, 528, 186, 70, 29, 14] }

theorem case_24_18_9_checked :
    (Witness.linear .conditional case_24_18_9).check 24 18 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_18_10 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 429, 429, 297] }

theorem case_24_18_10_checked :
    (Witness.linear .negative case_24_18_10).check 24 18 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_18_11 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 132] }

theorem case_24_18_11_checked :
    (Witness.linear .negative case_24_18_11).check 24 18 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_19_1_checked :
    (Witness.rising).check 24 19 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_19_2_checked :
    (Witness.rising).check 24 19 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_19_3_checked :
    (Witness.rising).check 24 19 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_19_4_checked :
    (Witness.rising).check 24 19 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_19_5_checked :
    (Witness.rising).check 24 19 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_19_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1, 1] }

theorem case_24_19_6_checked :
    (Witness.linear .positive case_24_19_6).check 24 19 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_19_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1] }

theorem case_24_19_7_checked :
    (Witness.linear .positive case_24_19_7).check 24 19 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_19_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2] }

theorem case_24_19_8_checked :
    (Witness.linear .positive case_24_19_8).check 24 19 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_19_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5] }

theorem case_24_19_9_checked :
    (Witness.linear .positive case_24_19_9).check 24 19 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_19_10 : Certificate := {
  objectiveScale := 504
  eta := 21109
  rows := #[⟨.assumptionRow 10, 359⟩]
  caps := #[0, 0, 9285, 3652, 2002, 145145] }

theorem case_24_19_10_checked :
    (Witness.linear .conditional case_24_19_10).check 24 19 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_19_11 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 429] }

theorem case_24_19_11_checked :
    (Witness.linear .negative case_24_19_11).check 24 19 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_19_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_24_19_12_checked :
    (Witness.linear .negative case_24_19_12).check 24 19 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_20_1_checked :
    (Witness.rising).check 24 20 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_20_2_checked :
    (Witness.rising).check 24 20 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_20_3_checked :
    (Witness.rising).check 24 20 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_20_4_checked :
    (Witness.rising).check 24 20 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_20_5_checked :
    (Witness.rising).check 24 20 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_20_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1] }

theorem case_24_20_6_checked :
    (Witness.linear .positive case_24_20_6).check 24 20 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_20_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2] }

theorem case_24_20_7_checked :
    (Witness.linear .positive case_24_20_7).check 24 20 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_20_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5] }

theorem case_24_20_8_checked :
    (Witness.linear .positive case_24_20_8).check 24 20 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_20_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14] }

theorem case_24_20_9_checked :
    (Witness.linear .positive case_24_20_9).check 24 20 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_20_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_24_20_10_checked :
    (Witness.linear .positive case_24_20_10).check 24 20 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_20_11 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 1430] }

theorem case_24_20_11_checked :
    (Witness.linear .negative case_24_20_11).check 24 20 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_20_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_24_20_12_checked :
    (Witness.linear .negative case_24_20_12).check 24 20 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_21_1_checked :
    (Witness.rising).check 24 21 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_21_2_checked :
    (Witness.rising).check 24 21 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_21_3_checked :
    (Witness.rising).check 24 21 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_21_4_checked :
    (Witness.rising).check 24 21 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_21_5_checked :
    (Witness.rising).check 24 21 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_21_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2] }

theorem case_24_21_6_checked :
    (Witness.linear .positive case_24_21_6).check 24 21 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_21_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5] }

theorem case_24_21_7_checked :
    (Witness.linear .positive case_24_21_7).check 24 21 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_21_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14] }

theorem case_24_21_8_checked :
    (Witness.linear .positive case_24_21_8).check 24 21 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_21_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_24_21_9_checked :
    (Witness.linear .positive case_24_21_9).check 24 21 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_21_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_24_21_10_checked :
    (Witness.linear .positive case_24_21_10).check 24 21 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_21_11 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 4862] }

theorem case_24_21_11_checked :
    (Witness.linear .negative case_24_21_11).check 24 21 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_21_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_24_21_12_checked :
    (Witness.linear .negative case_24_21_12).check 24 21 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_21_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_24_21_13_checked :
    (Witness.linear .negative case_24_21_13).check 24 21 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_22_1_checked :
    (Witness.rising).check 24 22 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_22_2_checked :
    (Witness.rising).check 24 22 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_22_3_checked :
    (Witness.rising).check 24 22 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_22_4_checked :
    (Witness.rising).check 24 22 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_22_5_checked :
    (Witness.rising).check 24 22 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_22_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5] }

theorem case_24_22_6_checked :
    (Witness.linear .positive case_24_22_6).check 24 22 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_22_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14] }

theorem case_24_22_7_checked :
    (Witness.linear .positive case_24_22_7).check 24 22 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_22_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42] }

theorem case_24_22_8_checked :
    (Witness.linear .positive case_24_22_8).check 24 22 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_22_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_24_22_9_checked :
    (Witness.linear .positive case_24_22_9).check 24 22 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_22_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_24_22_10_checked :
    (Witness.linear .positive case_24_22_10).check 24 22 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_22_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_24_22_11_checked :
    (Witness.linear .positive case_24_22_11).check 24 22 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_22_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_24_22_12_checked :
    (Witness.linear .negative case_24_22_12).check 24 22 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_22_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_24_22_13_checked :
    (Witness.linear .negative case_24_22_13).check 24 22 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_22_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_24_22_14_checked :
    (Witness.linear .negative case_24_22_14).check 24 22 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_23_1_checked :
    (Witness.rising).check 24 23 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_23_2_checked :
    (Witness.rising).check 24 23 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_23_3_checked :
    (Witness.rising).check 24 23 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_23_4_checked :
    (Witness.rising).check 24 23 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_24_23_5_checked :
    (Witness.rising).check 24 23 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_23_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0] }

theorem case_24_23_6_checked :
    (Witness.linear .positive case_24_23_6).check 24 23 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_23_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0] }

theorem case_24_23_7_checked :
    (Witness.linear .positive case_24_23_7).check 24 23 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_23_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0] }

theorem case_24_23_8_checked :
    (Witness.linear .positive case_24_23_8).check 24 23 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_23_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_24_23_9_checked :
    (Witness.linear .positive case_24_23_9).check 24 23 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_23_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_24_23_10_checked :
    (Witness.linear .positive case_24_23_10).check 24 23 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_23_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_24_23_11_checked :
    (Witness.linear .positive case_24_23_11).check 24 23 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_23_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_24_23_12_checked :
    (Witness.linear .negative case_24_23_12).check 24 23 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_23_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_24_23_13_checked :
    (Witness.linear .negative case_24_23_13).check 24 23 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_24_23_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_24_23_14_checked :
    (Witness.linear .negative case_24_23_14).check 24 23 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_24 (a k : ℕ) (h : Domain 24 a k) :
    ∃ w : Witness, w.check 24 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 12 ≤ a := by omega
  have haHi : a ≤ 23 := by omega
  interval_cases a

  · have hkHi : k ≤ 7 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_24_12_1_checked⟩

    · exact ⟨Witness.rising, case_24_12_2_checked⟩

    · exact ⟨Witness.rising, case_24_12_3_checked⟩

    · exact ⟨Witness.rising, case_24_12_4_checked⟩

    · exact ⟨Witness.rising, case_24_12_5_checked⟩

    · exact ⟨Witness.rising, case_24_12_6_checked⟩

    · exact ⟨Witness.linear .positive case_24_12_7, case_24_12_7_checked⟩

  · have hkHi : k ≤ 8 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_24_13_1_checked⟩

    · exact ⟨Witness.rising, case_24_13_2_checked⟩

    · exact ⟨Witness.rising, case_24_13_3_checked⟩

    · exact ⟨Witness.rising, case_24_13_4_checked⟩

    · exact ⟨Witness.rising, case_24_13_5_checked⟩

    · exact ⟨Witness.rising, case_24_13_6_checked⟩

    · exact ⟨Witness.linear .positive case_24_13_7, case_24_13_7_checked⟩

    · exact ⟨Witness.linear .conditional case_24_13_8, case_24_13_8_checked⟩

  · have hkHi : k ≤ 8 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_24_14_1_checked⟩

    · exact ⟨Witness.rising, case_24_14_2_checked⟩

    · exact ⟨Witness.rising, case_24_14_3_checked⟩

    · exact ⟨Witness.rising, case_24_14_4_checked⟩

    · exact ⟨Witness.rising, case_24_14_5_checked⟩

    · exact ⟨Witness.linear .positive case_24_14_6, case_24_14_6_checked⟩

    · exact ⟨Witness.linear .positive case_24_14_7, case_24_14_7_checked⟩

    · exact ⟨Witness.linear .conditional case_24_14_8, case_24_14_8_checked⟩

  · have hkHi : k ≤ 9 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_24_15_1_checked⟩

    · exact ⟨Witness.rising, case_24_15_2_checked⟩

    · exact ⟨Witness.rising, case_24_15_3_checked⟩

    · exact ⟨Witness.rising, case_24_15_4_checked⟩

    · exact ⟨Witness.rising, case_24_15_5_checked⟩

    · exact ⟨Witness.linear .positive case_24_15_6, case_24_15_6_checked⟩

    · exact ⟨Witness.linear .conditional case_24_15_7, case_24_15_7_checked⟩

    · exact ⟨Witness.linear .conditional case_24_15_8, case_24_15_8_checked⟩

    · exact ⟨Witness.linear .negative case_24_15_9, case_24_15_9_checked⟩

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_24_16_1_checked⟩

    · exact ⟨Witness.rising, case_24_16_2_checked⟩

    · exact ⟨Witness.rising, case_24_16_3_checked⟩

    · exact ⟨Witness.rising, case_24_16_4_checked⟩

    · exact ⟨Witness.rising, case_24_16_5_checked⟩

    · exact ⟨Witness.linear .positive case_24_16_6, case_24_16_6_checked⟩

    · exact ⟨Witness.linear .positive case_24_16_7, case_24_16_7_checked⟩

    · exact ⟨Witness.linear .conditional case_24_16_8, case_24_16_8_checked⟩

    · exact ⟨Witness.linear .conditional case_24_16_9, case_24_16_9_checked⟩

    · exact ⟨Witness.linear .negative case_24_16_10, case_24_16_10_checked⟩

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_24_17_1_checked⟩

    · exact ⟨Witness.rising, case_24_17_2_checked⟩

    · exact ⟨Witness.rising, case_24_17_3_checked⟩

    · exact ⟨Witness.rising, case_24_17_4_checked⟩

    · exact ⟨Witness.rising, case_24_17_5_checked⟩

    · exact ⟨Witness.linear .positive case_24_17_6, case_24_17_6_checked⟩

    · exact ⟨Witness.linear .positive case_24_17_7, case_24_17_7_checked⟩

    · exact ⟨Witness.linear .positive case_24_17_8, case_24_17_8_checked⟩

    · exact ⟨Witness.linear .conditional case_24_17_9, case_24_17_9_checked⟩

    · exact ⟨Witness.linear .negative case_24_17_10, case_24_17_10_checked⟩

  · have hkHi : k ≤ 11 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_24_18_1_checked⟩

    · exact ⟨Witness.rising, case_24_18_2_checked⟩

    · exact ⟨Witness.rising, case_24_18_3_checked⟩

    · exact ⟨Witness.rising, case_24_18_4_checked⟩

    · exact ⟨Witness.rising, case_24_18_5_checked⟩

    · exact ⟨Witness.linear .positive case_24_18_6, case_24_18_6_checked⟩

    · exact ⟨Witness.linear .positive case_24_18_7, case_24_18_7_checked⟩

    · exact ⟨Witness.linear .positive case_24_18_8, case_24_18_8_checked⟩

    · exact ⟨Witness.linear .conditional case_24_18_9, case_24_18_9_checked⟩

    · exact ⟨Witness.linear .negative case_24_18_10, case_24_18_10_checked⟩

    · exact ⟨Witness.linear .negative case_24_18_11, case_24_18_11_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_24_19_1_checked⟩

    · exact ⟨Witness.rising, case_24_19_2_checked⟩

    · exact ⟨Witness.rising, case_24_19_3_checked⟩

    · exact ⟨Witness.rising, case_24_19_4_checked⟩

    · exact ⟨Witness.rising, case_24_19_5_checked⟩

    · exact ⟨Witness.linear .positive case_24_19_6, case_24_19_6_checked⟩

    · exact ⟨Witness.linear .positive case_24_19_7, case_24_19_7_checked⟩

    · exact ⟨Witness.linear .positive case_24_19_8, case_24_19_8_checked⟩

    · exact ⟨Witness.linear .positive case_24_19_9, case_24_19_9_checked⟩

    · exact ⟨Witness.linear .conditional case_24_19_10, case_24_19_10_checked⟩

    · exact ⟨Witness.linear .negative case_24_19_11, case_24_19_11_checked⟩

    · exact ⟨Witness.linear .negative case_24_19_12, case_24_19_12_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_24_20_1_checked⟩

    · exact ⟨Witness.rising, case_24_20_2_checked⟩

    · exact ⟨Witness.rising, case_24_20_3_checked⟩

    · exact ⟨Witness.rising, case_24_20_4_checked⟩

    · exact ⟨Witness.rising, case_24_20_5_checked⟩

    · exact ⟨Witness.linear .positive case_24_20_6, case_24_20_6_checked⟩

    · exact ⟨Witness.linear .positive case_24_20_7, case_24_20_7_checked⟩

    · exact ⟨Witness.linear .positive case_24_20_8, case_24_20_8_checked⟩

    · exact ⟨Witness.linear .positive case_24_20_9, case_24_20_9_checked⟩

    · exact ⟨Witness.linear .positive case_24_20_10, case_24_20_10_checked⟩

    · exact ⟨Witness.linear .negative case_24_20_11, case_24_20_11_checked⟩

    · exact ⟨Witness.linear .negative case_24_20_12, case_24_20_12_checked⟩

  · have hkHi : k ≤ 13 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_24_21_1_checked⟩

    · exact ⟨Witness.rising, case_24_21_2_checked⟩

    · exact ⟨Witness.rising, case_24_21_3_checked⟩

    · exact ⟨Witness.rising, case_24_21_4_checked⟩

    · exact ⟨Witness.rising, case_24_21_5_checked⟩

    · exact ⟨Witness.linear .positive case_24_21_6, case_24_21_6_checked⟩

    · exact ⟨Witness.linear .positive case_24_21_7, case_24_21_7_checked⟩

    · exact ⟨Witness.linear .positive case_24_21_8, case_24_21_8_checked⟩

    · exact ⟨Witness.linear .positive case_24_21_9, case_24_21_9_checked⟩

    · exact ⟨Witness.linear .positive case_24_21_10, case_24_21_10_checked⟩

    · exact ⟨Witness.linear .negative case_24_21_11, case_24_21_11_checked⟩

    · exact ⟨Witness.linear .negative case_24_21_12, case_24_21_12_checked⟩

    · exact ⟨Witness.linear .negative case_24_21_13, case_24_21_13_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_24_22_1_checked⟩

    · exact ⟨Witness.rising, case_24_22_2_checked⟩

    · exact ⟨Witness.rising, case_24_22_3_checked⟩

    · exact ⟨Witness.rising, case_24_22_4_checked⟩

    · exact ⟨Witness.rising, case_24_22_5_checked⟩

    · exact ⟨Witness.linear .positive case_24_22_6, case_24_22_6_checked⟩

    · exact ⟨Witness.linear .positive case_24_22_7, case_24_22_7_checked⟩

    · exact ⟨Witness.linear .positive case_24_22_8, case_24_22_8_checked⟩

    · exact ⟨Witness.linear .positive case_24_22_9, case_24_22_9_checked⟩

    · exact ⟨Witness.linear .positive case_24_22_10, case_24_22_10_checked⟩

    · exact ⟨Witness.linear .positive case_24_22_11, case_24_22_11_checked⟩

    · exact ⟨Witness.linear .negative case_24_22_12, case_24_22_12_checked⟩

    · exact ⟨Witness.linear .negative case_24_22_13, case_24_22_13_checked⟩

    · exact ⟨Witness.linear .negative case_24_22_14, case_24_22_14_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_24_23_1_checked⟩

    · exact ⟨Witness.rising, case_24_23_2_checked⟩

    · exact ⟨Witness.rising, case_24_23_3_checked⟩

    · exact ⟨Witness.rising, case_24_23_4_checked⟩

    · exact ⟨Witness.rising, case_24_23_5_checked⟩

    · exact ⟨Witness.linear .positive case_24_23_6, case_24_23_6_checked⟩

    · exact ⟨Witness.linear .positive case_24_23_7, case_24_23_7_checked⟩

    · exact ⟨Witness.linear .positive case_24_23_8, case_24_23_8_checked⟩

    · exact ⟨Witness.linear .positive case_24_23_9, case_24_23_9_checked⟩

    · exact ⟨Witness.linear .positive case_24_23_10, case_24_23_10_checked⟩

    · exact ⟨Witness.linear .positive case_24_23_11, case_24_23_11_checked⟩

    · exact ⟨Witness.linear .negative case_24_23_12, case_24_23_12_checked⟩

    · exact ⟨Witness.linear .negative case_24_23_13, case_24_23_13_checked⟩

    · exact ⟨Witness.linear .negative case_24_23_14, case_24_23_14_checked⟩


#print axioms coverage_24
end ForestUnimodality.FiniteRows.FiniteData
