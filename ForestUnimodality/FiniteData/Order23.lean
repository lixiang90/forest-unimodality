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

theorem case_23_12_1_checked :
    (Witness.rising).check 23 12 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_12_2_checked :
    (Witness.rising).check 23 12 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_12_3_checked :
    (Witness.rising).check 23 12 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_12_4_checked :
    (Witness.rising).check 23 12 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_12_5_checked :
    (Witness.rising).check 23 12 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_12_6 : Certificate := {
  objectiveScale := 7350000
  eta := 539784000
  rows := #[⟨.count 2, 103088160⟩, ⟨.count 3, 23355360⟩, ⟨.count 4, 8749440⟩, ⟨.count 5, 7345800⟩, ⟨.path 6, 1405140⟩, ⟨.path 7, 1863400⟩, ⟨.privateRow 6 0, 393300⟩, ⟨.privateRow 7 0, 310380⟩, ⟨.hall 4 3, 80199⟩, ⟨.hall 3 6, 92680⟩]
  caps := #[0, 81480, 68040, 20160, 20440, 5355, 0, 1120, 0, 0, 0, 0] }

theorem case_23_12_6_checked :
    (Witness.linear .positive case_23_12_6).check 23 12 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_12_7 : Certificate := {
  objectiveScale := 4500000
  eta := 506179800
  rows := #[⟨.count 2, 111079080⟩, ⟨.count 3, 32263560⟩, ⟨.count 4, 12700800⟩, ⟨.count 5, 7408800⟩, ⟨.count 6, 7011900⟩, ⟨.count 8, 4498200⟩, ⟨.path 7, 2381540⟩, ⟨.privateRow 3 9, 1228920⟩, ⟨.privateRow 5 3, 265104⟩, ⟨.privateRow 6 1, 397250⟩, ⟨.privateRow 7 0, 360360⟩, ⟨.hall 5 5, 256650⟩, ⟨.hall 3 7, 618625⟩, ⟨.hall 4 7, 4282110⟩, ⟨.assumptionRow 7, 7407540⟩]
  caps := #[0, 91680, 12600, 5880, 0, 546, 0, 1040, 1800, 0, 0, 0] }

theorem case_23_12_7_checked :
    (Witness.linear .conditional case_23_12_7).check 23 12 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_13_1_checked :
    (Witness.rising).check 23 13 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_13_2_checked :
    (Witness.rising).check 23 13 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_13_3_checked :
    (Witness.rising).check 23 13 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_13_4_checked :
    (Witness.rising).check 23 13 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_13_5_checked :
    (Witness.rising).check 23 13 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_13_6 : Certificate := {
  objectiveScale := 4586400
  eta := 540736560
  rows := #[⟨.count 2, 96314400⟩, ⟨.count 3, 19641258⟩, ⟨.count 4, 6230952⟩, ⟨.count 5, 4586400⟩, ⟨.path 6, 1638070⟩, ⟨.path 7, 655200⟩, ⟨.privateRow 6 2, 99918⟩, ⟨.privateRow 7 0, 93366⟩, ⟨.hall 4 3, 2574⟩, ⟨.hall 5 5, 17745⟩]
  caps := #[0, 0, 14700, 16142, 0, 16940, 0, 1638, 0, 0, 0] }

theorem case_23_13_6_checked :
    (Witness.linear .positive case_23_13_6).check 23 13 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_13_7 : Certificate := {
  objectiveScale := 13200000
  eta := 2740620960
  rows := #[⟨.count 2, 554436960⟩, ⟨.count 3, 151448220⟩, ⟨.count 4, 50893920⟩, ⟨.count 5, 27627600⟩, ⟨.count 6, 25890480⟩, ⟨.path 7, 8800176⟩, ⟨.privateRow 4 6, 4029795⟩, ⟨.privateRow 4 7, 7253400⟩, ⟨.privateRow 5 4, 5484864⟩, ⟨.privateRow 5 5, 1700160⟩, ⟨.privateRow 6 1, 880440⟩, ⟨.privateRow 6 2, 2534840⟩, ⟨.privateRow 7 0, 2017620⟩, ⟨.privateRow 8 0, 2199120⟩, ⟨.hall 3 9, 911988⟩, ⟨.hall 2 10, 12489120⟩, ⟨.assumptionRow 7, 27640998⟩]
  caps := #[0, 0, 12936, 107100, 0, 33264, 1804, 0, 5280, 0, 0] }

theorem case_23_13_7_checked :
    (Witness.linear .conditional case_23_13_7).check 23 13 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_13_8 : Certificate := {
  objectiveScale := 568400000
  eta := 93793502880
  rows := #[⟨.count 2, 17811837120⟩, ⟨.count 3, 3030225660⟩, ⟨.count 6, 855328320⟩, ⟨.count 7, 5115088440⟩, ⟨.count 8, 2273372640⟩, ⟨.count 9, 573970320⟩, ⟨.path 3, 3031551600⟩, ⟨.privateRow 2 10, 2083924920⟩, ⟨.privateRow 3 7, 615705090⟩, ⟨.privateRow 3 8, 1255169300⟩, ⟨.privateRow 4 4, 81191880⟩, ⟨.privateRow 4 5, 419544972⟩, ⟨.privateRow 4 6, 585325125⟩, ⟨.privateRow 4 7, 467188260⟩, ⟨.privateRow 5 2, 40615080⟩, ⟨.privateRow 5 3, 234598980⟩, ⟨.privateRow 5 4, 350062944⟩, ⟨.privateRow 6 0, 24350865⟩, ⟨.privateRow 6 1, 101939640⟩, ⟨.privateRow 6 2, 73599680⟩, ⟨.hall 2 10, 1825928160⟩, ⟨.hall 1 11, 2084862780⟩]
  caps := #[0, 3104640, 0, 1695400, 2069991, 0, 1827725, 511560, 227360, 0, 0] }

theorem case_23_13_8_checked :
    (Witness.linear .negative case_23_13_8).check 23 13 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_14_1_checked :
    (Witness.rising).check 23 14 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_14_2_checked :
    (Witness.rising).check 23 14 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_14_3_checked :
    (Witness.rising).check 23 14 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_14_4_checked :
    (Witness.rising).check 23 14 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_14_5_checked :
    (Witness.rising).check 23 14 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_14_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_23_14_6_checked :
    (Witness.linear .positive case_23_14_6).check 23 14 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_14_7 : Certificate := {
  objectiveScale := 90000
  eta := 16632000
  rows := #[⟨.count 2, 4535685⟩, ⟨.count 3, 1259280⟩, ⟨.count 4, 396000⟩, ⟨.count 5, 162360⟩, ⟨.count 6, 126225⟩, ⟨.path 6, 36001⟩]
  caps := #[0, 792, 441, 755, 6, 0, 0, 0, 0, 0] }

theorem case_23_14_7_checked :
    (Witness.linear .positive case_23_14_7).check 23 14 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_14_8 : Certificate := {
  objectiveScale := 27751758000000
  eta := 6448886919820800
  rows := #[⟨.count 2, 1396007783377200⟩, ⟨.count 3, 355616577363600⟩, ⟨.count 4, 92779677345600⟩, ⟨.count 5, 25409509624800⟩, ⟨.count 9, 29372460667200⟩, ⟨.path 4, 33093685522800⟩, ⟨.path 5, 11171055319200⟩, ⟨.privateRow 2 12, 112798407978900⟩, ⟨.privateRow 3 9, 66515413574400⟩, ⟨.privateRow 3 10, 65213856124200⟩, ⟨.privateRow 4 6, 13066082701560⟩, ⟨.privateRow 4 7, 44226242239725⟩, ⟨.privateRow 4 8, 30955698461100⟩, ⟨.privateRow 5 4, 13940263078560⟩, ⟨.privateRow 5 5, 28258172079984⟩, ⟨.privateRow 5 6, 798418077660⟩, ⟨.privateRow 6 2, 10344467794500⟩, ⟨.privateRow 6 3, 8829221807700⟩, ⟨.privateRow 7 0, 2149026760125⟩, ⟨.privateRow 7 1, 5378290700400⟩, ⟨.privateRow 8 0, 2535123093300⟩, ⟨.hall 2 11, 8532971791050⟩, ⟨.assumptionRow 8, 14252377850200⟩]
  caps := #[0, 438028425600, 676623440100, 60761926050, 3605004600, 124523550816, 71229512200, 0, 285380578100, 0] }

theorem case_23_14_8_checked :
    (Witness.linear .conditional case_23_14_8).check 23 14 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_15_1_checked :
    (Witness.rising).check 23 15 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_15_2_checked :
    (Witness.rising).check 23 15 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_15_3_checked :
    (Witness.rising).check 23 15 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_15_4_checked :
    (Witness.rising).check 23 15 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_15_5_checked :
    (Witness.rising).check 23 15 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_15_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1, 1, 0, 0, 0] }

theorem case_23_15_6_checked :
    (Witness.linear .positive case_23_15_6).check 23 15 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_15_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0, 0] }

theorem case_23_15_7_checked :
    (Witness.linear .positive case_23_15_7).check 23 15 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_15_8 : Certificate := {
  objectiveScale := 25200000
  eta := 13441150800
  rows := #[⟨.count 2, 2565486000⟩, ⟨.count 3, 537629400⟩, ⟨.count 4, 111101760⟩, ⟨.count 5, 17047800⟩, ⟨.path 4, 84795480⟩, ⟨.privateRow 2 13, 108939600⟩, ⟨.privateRow 3 9, 49203000⟩, ⟨.privateRow 3 10, 106260000⟩, ⟨.privateRow 3 11, 28759500⟩, ⟨.privateRow 4 6, 11198880⟩, ⟨.privateRow 4 7, 62087256⟩, ⟨.privateRow 4 8, 38212020⟩, ⟨.privateRow 5 4, 18699120⟩, ⟨.privateRow 5 5, 33388740⟩, ⟨.privateRow 6 2, 20287575⟩, ⟨.privateRow 7 0, 7068600⟩, ⟨.privateRow 8 0, 2182950⟩, ⟨.assumptionRow 8, 17197600⟩]
  caps := #[0, 0, 517440, 129360, 86520, 254040, 133875, 0, 9574250] }

theorem case_23_15_8_checked :
    (Witness.linear .conditional case_23_15_8).check 23 15 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_15_9 : Certificate := {
  objectiveScale := 13
  eta := 58
  rows := #[⟨.assumptionRow 9, 6⟩]
  caps := #[0, 0, 29, 17, 11, 6, 258, 244, 146] }

theorem case_23_15_9_checked :
    (Witness.linear .conditional case_23_15_9).check 23 15 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_16_1_checked :
    (Witness.rising).check 23 16 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_16_2_checked :
    (Witness.rising).check 23 16 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_16_3_checked :
    (Witness.rising).check 23 16 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_16_4_checked :
    (Witness.rising).check 23 16 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_16_5_checked :
    (Witness.rising).check 23 16 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_16_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1, 1, 0, 0] }

theorem case_23_16_6_checked :
    (Witness.linear .positive case_23_16_6).check 23 16 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_16_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0] }

theorem case_23_16_7_checked :
    (Witness.linear .positive case_23_16_7).check 23 16 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_16_8 : Certificate := {
  objectiveScale := 2
  eta := 120
  rows := #[⟨.assumptionRow 8, 3⟩]
  caps := #[0, 0, 44, 17, 7, 4, 45, 30] }

theorem case_23_16_8_checked :
    (Witness.linear .conditional case_23_16_8).check 23 16 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_16_9 : Certificate := {
  objectiveScale := 24
  eta := 585
  rows := #[⟨.assumptionRow 9, 19⟩]
  caps := #[0, 0, 264, 122, 52, 33, 735, 639] }

theorem case_23_16_9_checked :
    (Witness.linear .conditional case_23_16_9).check 23 16 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_16_10 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 42, 42] }

theorem case_23_16_10_checked :
    (Witness.linear .negative case_23_16_10).check 23 16 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_17_1_checked :
    (Witness.rising).check 23 17 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_17_2_checked :
    (Witness.rising).check 23 17 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_17_3_checked :
    (Witness.rising).check 23 17 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_17_4_checked :
    (Witness.rising).check 23 17 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_17_5_checked :
    (Witness.rising).check 23 17 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_17_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1, 1, 0] }

theorem case_23_17_6_checked :
    (Witness.linear .positive case_23_17_6).check 23 17 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_17_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1] }

theorem case_23_17_7_checked :
    (Witness.linear .positive case_23_17_7).check 23 17 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_17_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1] }

theorem case_23_17_8_checked :
    (Witness.linear .positive case_23_17_8).check 23 17 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_17_9 : Certificate := {
  objectiveScale := 6
  eta := 165
  rows := #[⟨.assumptionRow 9, 5⟩]
  caps := #[0, 0, 78, 34, 15, 407, 440] }

theorem case_23_17_9_checked :
    (Witness.linear .conditional case_23_17_9).check 23 17 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_17_10 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 132, 132] }

theorem case_23_17_10_checked :
    (Witness.linear .negative case_23_17_10).check 23 17 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_18_1_checked :
    (Witness.rising).check 23 18 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_18_2_checked :
    (Witness.rising).check 23 18 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_18_3_checked :
    (Witness.rising).check 23 18 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_18_4_checked :
    (Witness.rising).check 23 18 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_18_5_checked :
    (Witness.rising).check 23 18 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_18_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1, 1] }

theorem case_23_18_6_checked :
    (Witness.linear .positive case_23_18_6).check 23 18 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_18_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1] }

theorem case_23_18_7_checked :
    (Witness.linear .positive case_23_18_7).check 23 18 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_18_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2] }

theorem case_23_18_8_checked :
    (Witness.linear .positive case_23_18_8).check 23 18 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_18_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5] }

theorem case_23_18_9_checked :
    (Witness.linear .positive case_23_18_9).check 23 18 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_18_10 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 429, 429] }

theorem case_23_18_10_checked :
    (Witness.linear .negative case_23_18_10).check 23 18 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_18_11 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_23_18_11_checked :
    (Witness.linear .negative case_23_18_11).check 23 18 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_19_1_checked :
    (Witness.rising).check 23 19 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_19_2_checked :
    (Witness.rising).check 23 19 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_19_3_checked :
    (Witness.rising).check 23 19 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_19_4_checked :
    (Witness.rising).check 23 19 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_19_5_checked :
    (Witness.rising).check 23 19 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_19_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1] }

theorem case_23_19_6_checked :
    (Witness.linear .positive case_23_19_6).check 23 19 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_19_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2] }

theorem case_23_19_7_checked :
    (Witness.linear .positive case_23_19_7).check 23 19 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_19_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5] }

theorem case_23_19_8_checked :
    (Witness.linear .positive case_23_19_8).check 23 19 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_19_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14] }

theorem case_23_19_9_checked :
    (Witness.linear .positive case_23_19_9).check 23 19 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_19_10 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 1430, 1430] }

theorem case_23_19_10_checked :
    (Witness.linear .negative case_23_19_10).check 23 19 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_19_11 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_23_19_11_checked :
    (Witness.linear .negative case_23_19_11).check 23 19 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_19_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_23_19_12_checked :
    (Witness.linear .negative case_23_19_12).check 23 19 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_20_1_checked :
    (Witness.rising).check 23 20 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_20_2_checked :
    (Witness.rising).check 23 20 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_20_3_checked :
    (Witness.rising).check 23 20 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_20_4_checked :
    (Witness.rising).check 23 20 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_20_5_checked :
    (Witness.rising).check 23 20 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_20_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2] }

theorem case_23_20_6_checked :
    (Witness.linear .positive case_23_20_6).check 23 20 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_20_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5] }

theorem case_23_20_7_checked :
    (Witness.linear .positive case_23_20_7).check 23 20 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_20_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14] }

theorem case_23_20_8_checked :
    (Witness.linear .positive case_23_20_8).check 23 20 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_20_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_23_20_9_checked :
    (Witness.linear .positive case_23_20_9).check 23 20 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_20_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_23_20_10_checked :
    (Witness.linear .positive case_23_20_10).check 23 20 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_20_11 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_23_20_11_checked :
    (Witness.linear .negative case_23_20_11).check 23 20 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_20_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_23_20_12_checked :
    (Witness.linear .negative case_23_20_12).check 23 20 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_21_1_checked :
    (Witness.rising).check 23 21 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_21_2_checked :
    (Witness.rising).check 23 21 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_21_3_checked :
    (Witness.rising).check 23 21 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_21_4_checked :
    (Witness.rising).check 23 21 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_21_5_checked :
    (Witness.rising).check 23 21 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_21_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5] }

theorem case_23_21_6_checked :
    (Witness.linear .positive case_23_21_6).check 23 21 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_21_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14] }

theorem case_23_21_7_checked :
    (Witness.linear .positive case_23_21_7).check 23 21 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_21_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42] }

theorem case_23_21_8_checked :
    (Witness.linear .positive case_23_21_8).check 23 21 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_21_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_23_21_9_checked :
    (Witness.linear .positive case_23_21_9).check 23 21 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_21_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_23_21_10_checked :
    (Witness.linear .positive case_23_21_10).check 23 21 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_21_11 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_23_21_11_checked :
    (Witness.linear .negative case_23_21_11).check 23 21 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_21_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_23_21_12_checked :
    (Witness.linear .negative case_23_21_12).check 23 21 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_21_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_23_21_13_checked :
    (Witness.linear .negative case_23_21_13).check 23 21 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_22_1_checked :
    (Witness.rising).check 23 22 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_22_2_checked :
    (Witness.rising).check 23 22 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_22_3_checked :
    (Witness.rising).check 23 22 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_22_4_checked :
    (Witness.rising).check 23 22 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_23_22_5_checked :
    (Witness.rising).check 23 22 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_22_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0] }

theorem case_23_22_6_checked :
    (Witness.linear .positive case_23_22_6).check 23 22 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_22_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0] }

theorem case_23_22_7_checked :
    (Witness.linear .positive case_23_22_7).check 23 22 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_22_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0] }

theorem case_23_22_8_checked :
    (Witness.linear .positive case_23_22_8).check 23 22 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_22_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_23_22_9_checked :
    (Witness.linear .positive case_23_22_9).check 23 22 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_22_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_23_22_10_checked :
    (Witness.linear .positive case_23_22_10).check 23 22 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_22_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_23_22_11_checked :
    (Witness.linear .positive case_23_22_11).check 23 22 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_22_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_23_22_12_checked :
    (Witness.linear .negative case_23_22_12).check 23 22 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_22_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_23_22_13_checked :
    (Witness.linear .negative case_23_22_13).check 23 22 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_23_22_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_23_22_14_checked :
    (Witness.linear .negative case_23_22_14).check 23 22 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_23 (a k : ℕ) (h : Domain 23 a k) :
    ∃ w : Witness, w.check 23 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 12 ≤ a := by omega
  have haHi : a ≤ 22 := by omega
  interval_cases a

  · have hkHi : k ≤ 7 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_23_12_1_checked⟩

    · exact ⟨Witness.rising, case_23_12_2_checked⟩

    · exact ⟨Witness.rising, case_23_12_3_checked⟩

    · exact ⟨Witness.rising, case_23_12_4_checked⟩

    · exact ⟨Witness.rising, case_23_12_5_checked⟩

    · exact ⟨Witness.linear .positive case_23_12_6, case_23_12_6_checked⟩

    · exact ⟨Witness.linear .conditional case_23_12_7, case_23_12_7_checked⟩

  · have hkHi : k ≤ 8 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_23_13_1_checked⟩

    · exact ⟨Witness.rising, case_23_13_2_checked⟩

    · exact ⟨Witness.rising, case_23_13_3_checked⟩

    · exact ⟨Witness.rising, case_23_13_4_checked⟩

    · exact ⟨Witness.rising, case_23_13_5_checked⟩

    · exact ⟨Witness.linear .positive case_23_13_6, case_23_13_6_checked⟩

    · exact ⟨Witness.linear .conditional case_23_13_7, case_23_13_7_checked⟩

    · exact ⟨Witness.linear .negative case_23_13_8, case_23_13_8_checked⟩

  · have hkHi : k ≤ 8 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_23_14_1_checked⟩

    · exact ⟨Witness.rising, case_23_14_2_checked⟩

    · exact ⟨Witness.rising, case_23_14_3_checked⟩

    · exact ⟨Witness.rising, case_23_14_4_checked⟩

    · exact ⟨Witness.rising, case_23_14_5_checked⟩

    · exact ⟨Witness.linear .positive case_23_14_6, case_23_14_6_checked⟩

    · exact ⟨Witness.linear .positive case_23_14_7, case_23_14_7_checked⟩

    · exact ⟨Witness.linear .conditional case_23_14_8, case_23_14_8_checked⟩

  · have hkHi : k ≤ 9 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_23_15_1_checked⟩

    · exact ⟨Witness.rising, case_23_15_2_checked⟩

    · exact ⟨Witness.rising, case_23_15_3_checked⟩

    · exact ⟨Witness.rising, case_23_15_4_checked⟩

    · exact ⟨Witness.rising, case_23_15_5_checked⟩

    · exact ⟨Witness.linear .positive case_23_15_6, case_23_15_6_checked⟩

    · exact ⟨Witness.linear .positive case_23_15_7, case_23_15_7_checked⟩

    · exact ⟨Witness.linear .conditional case_23_15_8, case_23_15_8_checked⟩

    · exact ⟨Witness.linear .conditional case_23_15_9, case_23_15_9_checked⟩

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_23_16_1_checked⟩

    · exact ⟨Witness.rising, case_23_16_2_checked⟩

    · exact ⟨Witness.rising, case_23_16_3_checked⟩

    · exact ⟨Witness.rising, case_23_16_4_checked⟩

    · exact ⟨Witness.rising, case_23_16_5_checked⟩

    · exact ⟨Witness.linear .positive case_23_16_6, case_23_16_6_checked⟩

    · exact ⟨Witness.linear .positive case_23_16_7, case_23_16_7_checked⟩

    · exact ⟨Witness.linear .conditional case_23_16_8, case_23_16_8_checked⟩

    · exact ⟨Witness.linear .conditional case_23_16_9, case_23_16_9_checked⟩

    · exact ⟨Witness.linear .negative case_23_16_10, case_23_16_10_checked⟩

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_23_17_1_checked⟩

    · exact ⟨Witness.rising, case_23_17_2_checked⟩

    · exact ⟨Witness.rising, case_23_17_3_checked⟩

    · exact ⟨Witness.rising, case_23_17_4_checked⟩

    · exact ⟨Witness.rising, case_23_17_5_checked⟩

    · exact ⟨Witness.linear .positive case_23_17_6, case_23_17_6_checked⟩

    · exact ⟨Witness.linear .positive case_23_17_7, case_23_17_7_checked⟩

    · exact ⟨Witness.linear .positive case_23_17_8, case_23_17_8_checked⟩

    · exact ⟨Witness.linear .conditional case_23_17_9, case_23_17_9_checked⟩

    · exact ⟨Witness.linear .negative case_23_17_10, case_23_17_10_checked⟩

  · have hkHi : k ≤ 11 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_23_18_1_checked⟩

    · exact ⟨Witness.rising, case_23_18_2_checked⟩

    · exact ⟨Witness.rising, case_23_18_3_checked⟩

    · exact ⟨Witness.rising, case_23_18_4_checked⟩

    · exact ⟨Witness.rising, case_23_18_5_checked⟩

    · exact ⟨Witness.linear .positive case_23_18_6, case_23_18_6_checked⟩

    · exact ⟨Witness.linear .positive case_23_18_7, case_23_18_7_checked⟩

    · exact ⟨Witness.linear .positive case_23_18_8, case_23_18_8_checked⟩

    · exact ⟨Witness.linear .positive case_23_18_9, case_23_18_9_checked⟩

    · exact ⟨Witness.linear .negative case_23_18_10, case_23_18_10_checked⟩

    · exact ⟨Witness.linear .negative case_23_18_11, case_23_18_11_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_23_19_1_checked⟩

    · exact ⟨Witness.rising, case_23_19_2_checked⟩

    · exact ⟨Witness.rising, case_23_19_3_checked⟩

    · exact ⟨Witness.rising, case_23_19_4_checked⟩

    · exact ⟨Witness.rising, case_23_19_5_checked⟩

    · exact ⟨Witness.linear .positive case_23_19_6, case_23_19_6_checked⟩

    · exact ⟨Witness.linear .positive case_23_19_7, case_23_19_7_checked⟩

    · exact ⟨Witness.linear .positive case_23_19_8, case_23_19_8_checked⟩

    · exact ⟨Witness.linear .positive case_23_19_9, case_23_19_9_checked⟩

    · exact ⟨Witness.linear .negative case_23_19_10, case_23_19_10_checked⟩

    · exact ⟨Witness.linear .negative case_23_19_11, case_23_19_11_checked⟩

    · exact ⟨Witness.linear .negative case_23_19_12, case_23_19_12_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_23_20_1_checked⟩

    · exact ⟨Witness.rising, case_23_20_2_checked⟩

    · exact ⟨Witness.rising, case_23_20_3_checked⟩

    · exact ⟨Witness.rising, case_23_20_4_checked⟩

    · exact ⟨Witness.rising, case_23_20_5_checked⟩

    · exact ⟨Witness.linear .positive case_23_20_6, case_23_20_6_checked⟩

    · exact ⟨Witness.linear .positive case_23_20_7, case_23_20_7_checked⟩

    · exact ⟨Witness.linear .positive case_23_20_8, case_23_20_8_checked⟩

    · exact ⟨Witness.linear .positive case_23_20_9, case_23_20_9_checked⟩

    · exact ⟨Witness.linear .positive case_23_20_10, case_23_20_10_checked⟩

    · exact ⟨Witness.linear .negative case_23_20_11, case_23_20_11_checked⟩

    · exact ⟨Witness.linear .negative case_23_20_12, case_23_20_12_checked⟩

  · have hkHi : k ≤ 13 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_23_21_1_checked⟩

    · exact ⟨Witness.rising, case_23_21_2_checked⟩

    · exact ⟨Witness.rising, case_23_21_3_checked⟩

    · exact ⟨Witness.rising, case_23_21_4_checked⟩

    · exact ⟨Witness.rising, case_23_21_5_checked⟩

    · exact ⟨Witness.linear .positive case_23_21_6, case_23_21_6_checked⟩

    · exact ⟨Witness.linear .positive case_23_21_7, case_23_21_7_checked⟩

    · exact ⟨Witness.linear .positive case_23_21_8, case_23_21_8_checked⟩

    · exact ⟨Witness.linear .positive case_23_21_9, case_23_21_9_checked⟩

    · exact ⟨Witness.linear .positive case_23_21_10, case_23_21_10_checked⟩

    · exact ⟨Witness.linear .negative case_23_21_11, case_23_21_11_checked⟩

    · exact ⟨Witness.linear .negative case_23_21_12, case_23_21_12_checked⟩

    · exact ⟨Witness.linear .negative case_23_21_13, case_23_21_13_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_23_22_1_checked⟩

    · exact ⟨Witness.rising, case_23_22_2_checked⟩

    · exact ⟨Witness.rising, case_23_22_3_checked⟩

    · exact ⟨Witness.rising, case_23_22_4_checked⟩

    · exact ⟨Witness.rising, case_23_22_5_checked⟩

    · exact ⟨Witness.linear .positive case_23_22_6, case_23_22_6_checked⟩

    · exact ⟨Witness.linear .positive case_23_22_7, case_23_22_7_checked⟩

    · exact ⟨Witness.linear .positive case_23_22_8, case_23_22_8_checked⟩

    · exact ⟨Witness.linear .positive case_23_22_9, case_23_22_9_checked⟩

    · exact ⟨Witness.linear .positive case_23_22_10, case_23_22_10_checked⟩

    · exact ⟨Witness.linear .positive case_23_22_11, case_23_22_11_checked⟩

    · exact ⟨Witness.linear .negative case_23_22_12, case_23_22_12_checked⟩

    · exact ⟨Witness.linear .negative case_23_22_13, case_23_22_13_checked⟩

    · exact ⟨Witness.linear .negative case_23_22_14, case_23_22_14_checked⟩


#print axioms coverage_23
end ForestUnimodality.FiniteRows.FiniteData
