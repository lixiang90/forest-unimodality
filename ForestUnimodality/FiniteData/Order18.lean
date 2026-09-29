import ForestUnimodality.FiniteWitness
import Mathlib.Tactic.IntervalCases

/-! Generated candidate witnesses. Each sign is rechecked by the Lean kernel.
The coverage theorem quantifies over Domain, independently of this record list.
Source and integer-witness hashes are recorded in research/finite-integer-witnesses/manifest.json.
-/
namespace ForestUnimodality.FiniteRows.FiniteData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_18_9_1_checked :
    (Witness.rising).check 18 9 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_9_2_checked :
    (Witness.rising).check 18 9 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_9_3_checked :
    (Witness.rising).check 18 9 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_9_4_checked :
    (Witness.rising).check 18 9 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_9_5 : Certificate := {
  objectiveScale := 26800000
  eta := 29940960
  rows := #[⟨.count 2, 150098760⟩, ⟨.count 3, 38592000⟩, ⟨.count 4, 26805360⟩, ⟨.path 5, 11792520⟩, ⟨.path 6, 3216402⟩, ⟨.privateRow 6 0, 1697445⟩, ⟨.hall 0 2, 21442680⟩, ⟨.hall 4 2, 1000712⟩]
  caps := #[0, 58912, 13510, 1962, 0, 1324, 0, 0, 0, 0] }

theorem case_18_9_5_checked :
    (Witness.linear .positive case_18_9_5).check 18 9 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_10_1_checked :
    (Witness.rising).check 18 10 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_10_2_checked :
    (Witness.rising).check 18 10 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_10_3_checked :
    (Witness.rising).check 18 10 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_10_4_checked :
    (Witness.rising).check 18 10 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_10_5 : Certificate := {
  objectiveScale := 1875000
  eta := 53544750
  rows := #[⟨.count 2, 10500000⟩, ⟨.count 3, 2701125⟩, ⟨.count 4, 1875300⟩, ⟨.path 5, 824964⟩, ⟨.path 6, 225000⟩, ⟨.privateRow 6 0, 99925⟩, ⟨.hall 4 2, 35000⟩]
  caps := #[0, 714, 0, 0, 0, 0, 0, 0, 0] }

theorem case_18_10_5_checked :
    (Witness.linear .positive case_18_10_5).check 18 10 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_10_6 : Certificate := {
  objectiveScale := 45000000
  eta := 547501500
  rows := #[⟨.count 2, 175329000⟩, ⟨.count 3, 77805000⟩, ⟨.count 4, 76658400⟩, ⟨.count 5, 14332500⟩, ⟨.count 7, 44982000⟩, ⟨.path 5, 19344528⟩, ⟨.privateRow 3 5, 5257000⟩, ⟨.privateRow 4 3, 7445025⟩, ⟨.privateRow 4 4, 2868600⟩, ⟨.privateRow 5 0, 6233850⟩, ⟨.privateRow 6 0, 4105500⟩, ⟨.hall 2 7, 10087875⟩, ⟨.assumptionRow 6, 32379750⟩]
  caps := #[0, 0, 15030, 0, 1278, 0, 0, 18000, 0] }

theorem case_18_10_6_checked :
    (Witness.linear .conditional case_18_10_6).check 18 10 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_11_1_checked :
    (Witness.rising).check 18 11 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_11_2_checked :
    (Witness.rising).check 18 11 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_11_3_checked :
    (Witness.rising).check 18 11 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_11_4_checked :
    (Witness.rising).check 18 11 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_11_5 : Certificate := {
  objectiveScale := 109375
  eta := 3280725
  rows := #[⟨.count 2, 702975⟩, ⟨.count 3, 187425⟩, ⟨.count 4, 109305⟩, ⟨.path 5, 62500⟩, ⟨.hall 3 4, 2232⟩]
  caps := #[0, 525, 150, 75, 70, 0, 0, 0] }

theorem case_18_11_5_checked :
    (Witness.linear .positive case_18_11_5).check 18 11 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_11_6 : Certificate := {
  objectiveScale := 20700000
  eta := 710010000
  rows := #[⟨.count 2, 185810100⟩, ⟨.count 3, 67929120⟩, ⟨.count 4, 34920900⟩, ⟨.count 5, 5844300⟩, ⟨.path 4, 18803260⟩, ⟨.privateRow 3 5, 1895775⟩, ⟨.privateRow 3 6, 9859640⟩, ⟨.privateRow 4 3, 6597297⟩, ⟨.privateRow 4 4, 2187990⟩, ⟨.privateRow 5 1, 5142340⟩, ⟨.privateRow 6 0, 2817500⟩, ⟨.privateRow 7 0, 4144140⟩, ⟨.assumptionRow 6, 16117020⟩]
  caps := #[0, 66360, 7600, 15598, 8281, 0, 61180, 0] }

theorem case_18_11_6_checked :
    (Witness.linear .conditional case_18_11_6).check 18 11 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_12_1_checked :
    (Witness.rising).check 18 12 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_12_2_checked :
    (Witness.rising).check 18 12 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_12_3_checked :
    (Witness.rising).check 18 12 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_12_4_checked :
    (Witness.rising).check 18 12 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_12_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0, 2, 1, 1, 0, 0] }

theorem case_18_12_5_checked :
    (Witness.linear .positive case_18_12_5).check 18 12 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_12_6 : Certificate := {
  objectiveScale := 2
  eta := 17
  rows := #[⟨.assumptionRow 6, 3⟩]
  caps := #[0, 0, 7, 4, 3, 10, 7] }

theorem case_18_12_6_checked :
    (Witness.linear .conditional case_18_12_6).check 18 12 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_12_7 : Certificate := {
  objectiveScale := 29
  eta := 41
  rows := #[⟨.assumptionRow 7, 14⟩]
  caps := #[0, 0, 27, 14, 14, 210, 191] }

theorem case_18_12_7_checked :
    (Witness.linear .conditional case_18_12_7).check 18 12 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_13_1_checked :
    (Witness.rising).check 18 13 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_13_2_checked :
    (Witness.rising).check 18 13 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_13_3_checked :
    (Witness.rising).check 18 13 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_13_4_checked :
    (Witness.rising).check 18 13 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_13_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0, 2, 1, 1, 0] }

theorem case_18_13_5_checked :
    (Witness.linear .positive case_18_13_5).check 18 13 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_13_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1, 1] }

theorem case_18_13_6_checked :
    (Witness.linear .positive case_18_13_6).check 18 13 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_13_7 : Certificate := {
  objectiveScale := 7
  eta := 42
  rows := #[⟨.assumptionRow 7, 6⟩]
  caps := #[0, 0, 19, 11, 6, 76] }

theorem case_18_13_7_checked :
    (Witness.linear .conditional case_18_13_7).check 18 13 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_13_8 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 14] }

theorem case_18_13_8_checked :
    (Witness.linear .negative case_18_13_8).check 18 13 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_14_1_checked :
    (Witness.rising).check 18 14 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_14_2_checked :
    (Witness.rising).check 18 14 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_14_3_checked :
    (Witness.rising).check 18 14 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_14_4_checked :
    (Witness.rising).check 18 14 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_14_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0, 2, 1, 1] }

theorem case_18_14_5_checked :
    (Witness.linear .positive case_18_14_5).check 18 14 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_14_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1] }

theorem case_18_14_6_checked :
    (Witness.linear .positive case_18_14_6).check 18 14 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_14_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2] }

theorem case_18_14_7_checked :
    (Witness.linear .positive case_18_14_7).check 18 14 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_14_8 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 42] }

theorem case_18_14_8_checked :
    (Witness.linear .negative case_18_14_8).check 18 14 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_15_1_checked :
    (Witness.rising).check 18 15 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_15_2_checked :
    (Witness.rising).check 18 15 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_15_3_checked :
    (Witness.rising).check 18 15 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_15_4_checked :
    (Witness.rising).check 18 15 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_15_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0, 2, 1] }

theorem case_18_15_5_checked :
    (Witness.linear .positive case_18_15_5).check 18 15 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_15_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2] }

theorem case_18_15_6_checked :
    (Witness.linear .positive case_18_15_6).check 18 15 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_15_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5] }

theorem case_18_15_7_checked :
    (Witness.linear .positive case_18_15_7).check 18 15 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_15_8 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 132] }

theorem case_18_15_8_checked :
    (Witness.linear .negative case_18_15_8).check 18 15 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_15_9 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_18_15_9_checked :
    (Witness.linear .negative case_18_15_9).check 18 15 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_16_1_checked :
    (Witness.rising).check 18 16 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_16_2_checked :
    (Witness.rising).check 18 16 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_16_3_checked :
    (Witness.rising).check 18 16 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_16_4_checked :
    (Witness.rising).check 18 16 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_16_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0, 2] }

theorem case_18_16_5_checked :
    (Witness.linear .positive case_18_16_5).check 18 16 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_16_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5] }

theorem case_18_16_6_checked :
    (Witness.linear .positive case_18_16_6).check 18 16 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_16_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14] }

theorem case_18_16_7_checked :
    (Witness.linear .positive case_18_16_7).check 18 16 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_16_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42] }

theorem case_18_16_8_checked :
    (Witness.linear .positive case_18_16_8).check 18 16 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_16_9 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_18_16_9_checked :
    (Witness.linear .negative case_18_16_9).check 18 16 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_16_10 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_18_16_10_checked :
    (Witness.linear .negative case_18_16_10).check 18 16 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_17_1_checked :
    (Witness.rising).check 18 17 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_17_2_checked :
    (Witness.rising).check 18 17 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_17_3_checked :
    (Witness.rising).check 18 17 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_18_17_4_checked :
    (Witness.rising).check 18 17 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_17_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0] }

theorem case_18_17_5_checked :
    (Witness.linear .positive case_18_17_5).check 18 17 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_17_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0] }

theorem case_18_17_6_checked :
    (Witness.linear .positive case_18_17_6).check 18 17 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_17_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0] }

theorem case_18_17_7_checked :
    (Witness.linear .positive case_18_17_7).check 18 17 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_17_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0] }

theorem case_18_17_8_checked :
    (Witness.linear .positive case_18_17_8).check 18 17 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_17_9 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_18_17_9_checked :
    (Witness.linear .negative case_18_17_9).check 18 17 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_18_17_10 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_18_17_10_checked :
    (Witness.linear .negative case_18_17_10).check 18 17 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_18 (a k : ℕ) (h : Domain 18 a k) :
    ∃ w : Witness, w.check 18 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 9 ≤ a := by omega
  have haHi : a ≤ 17 := by omega
  interval_cases a

  · have hkHi : k ≤ 5 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_18_9_1_checked⟩

    · exact ⟨Witness.rising, case_18_9_2_checked⟩

    · exact ⟨Witness.rising, case_18_9_3_checked⟩

    · exact ⟨Witness.rising, case_18_9_4_checked⟩

    · exact ⟨Witness.linear .positive case_18_9_5, case_18_9_5_checked⟩

  · have hkHi : k ≤ 6 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_18_10_1_checked⟩

    · exact ⟨Witness.rising, case_18_10_2_checked⟩

    · exact ⟨Witness.rising, case_18_10_3_checked⟩

    · exact ⟨Witness.rising, case_18_10_4_checked⟩

    · exact ⟨Witness.linear .positive case_18_10_5, case_18_10_5_checked⟩

    · exact ⟨Witness.linear .conditional case_18_10_6, case_18_10_6_checked⟩

  · have hkHi : k ≤ 6 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_18_11_1_checked⟩

    · exact ⟨Witness.rising, case_18_11_2_checked⟩

    · exact ⟨Witness.rising, case_18_11_3_checked⟩

    · exact ⟨Witness.rising, case_18_11_4_checked⟩

    · exact ⟨Witness.linear .positive case_18_11_5, case_18_11_5_checked⟩

    · exact ⟨Witness.linear .conditional case_18_11_6, case_18_11_6_checked⟩

  · have hkHi : k ≤ 7 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_18_12_1_checked⟩

    · exact ⟨Witness.rising, case_18_12_2_checked⟩

    · exact ⟨Witness.rising, case_18_12_3_checked⟩

    · exact ⟨Witness.rising, case_18_12_4_checked⟩

    · exact ⟨Witness.linear .positive case_18_12_5, case_18_12_5_checked⟩

    · exact ⟨Witness.linear .conditional case_18_12_6, case_18_12_6_checked⟩

    · exact ⟨Witness.linear .conditional case_18_12_7, case_18_12_7_checked⟩

  · have hkHi : k ≤ 8 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_18_13_1_checked⟩

    · exact ⟨Witness.rising, case_18_13_2_checked⟩

    · exact ⟨Witness.rising, case_18_13_3_checked⟩

    · exact ⟨Witness.rising, case_18_13_4_checked⟩

    · exact ⟨Witness.linear .positive case_18_13_5, case_18_13_5_checked⟩

    · exact ⟨Witness.linear .positive case_18_13_6, case_18_13_6_checked⟩

    · exact ⟨Witness.linear .conditional case_18_13_7, case_18_13_7_checked⟩

    · exact ⟨Witness.linear .negative case_18_13_8, case_18_13_8_checked⟩

  · have hkHi : k ≤ 8 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_18_14_1_checked⟩

    · exact ⟨Witness.rising, case_18_14_2_checked⟩

    · exact ⟨Witness.rising, case_18_14_3_checked⟩

    · exact ⟨Witness.rising, case_18_14_4_checked⟩

    · exact ⟨Witness.linear .positive case_18_14_5, case_18_14_5_checked⟩

    · exact ⟨Witness.linear .positive case_18_14_6, case_18_14_6_checked⟩

    · exact ⟨Witness.linear .positive case_18_14_7, case_18_14_7_checked⟩

    · exact ⟨Witness.linear .negative case_18_14_8, case_18_14_8_checked⟩

  · have hkHi : k ≤ 9 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_18_15_1_checked⟩

    · exact ⟨Witness.rising, case_18_15_2_checked⟩

    · exact ⟨Witness.rising, case_18_15_3_checked⟩

    · exact ⟨Witness.rising, case_18_15_4_checked⟩

    · exact ⟨Witness.linear .positive case_18_15_5, case_18_15_5_checked⟩

    · exact ⟨Witness.linear .positive case_18_15_6, case_18_15_6_checked⟩

    · exact ⟨Witness.linear .positive case_18_15_7, case_18_15_7_checked⟩

    · exact ⟨Witness.linear .negative case_18_15_8, case_18_15_8_checked⟩

    · exact ⟨Witness.linear .negative case_18_15_9, case_18_15_9_checked⟩

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_18_16_1_checked⟩

    · exact ⟨Witness.rising, case_18_16_2_checked⟩

    · exact ⟨Witness.rising, case_18_16_3_checked⟩

    · exact ⟨Witness.rising, case_18_16_4_checked⟩

    · exact ⟨Witness.linear .positive case_18_16_5, case_18_16_5_checked⟩

    · exact ⟨Witness.linear .positive case_18_16_6, case_18_16_6_checked⟩

    · exact ⟨Witness.linear .positive case_18_16_7, case_18_16_7_checked⟩

    · exact ⟨Witness.linear .positive case_18_16_8, case_18_16_8_checked⟩

    · exact ⟨Witness.linear .negative case_18_16_9, case_18_16_9_checked⟩

    · exact ⟨Witness.linear .negative case_18_16_10, case_18_16_10_checked⟩

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_18_17_1_checked⟩

    · exact ⟨Witness.rising, case_18_17_2_checked⟩

    · exact ⟨Witness.rising, case_18_17_3_checked⟩

    · exact ⟨Witness.rising, case_18_17_4_checked⟩

    · exact ⟨Witness.linear .positive case_18_17_5, case_18_17_5_checked⟩

    · exact ⟨Witness.linear .positive case_18_17_6, case_18_17_6_checked⟩

    · exact ⟨Witness.linear .positive case_18_17_7, case_18_17_7_checked⟩

    · exact ⟨Witness.linear .positive case_18_17_8, case_18_17_8_checked⟩

    · exact ⟨Witness.linear .negative case_18_17_9, case_18_17_9_checked⟩

    · exact ⟨Witness.linear .negative case_18_17_10, case_18_17_10_checked⟩


#print axioms coverage_18
end ForestUnimodality.FiniteRows.FiniteData
