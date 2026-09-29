import ForestUnimodality.FiniteWitness
import Mathlib.Tactic.IntervalCases

/-! Generated candidate witnesses. Each sign is rechecked by the Lean kernel.
The coverage theorem quantifies over Domain, independently of this record list.
Source and integer-witness hashes are recorded in research/finite-integer-witnesses/manifest.json.
-/
namespace ForestUnimodality.FiniteRows.FiniteData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_19_10_1_checked :
    (Witness.rising).check 19 10 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_10_2_checked :
    (Witness.rising).check 19 10 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_10_3_checked :
    (Witness.rising).check 19 10 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_10_4_checked :
    (Witness.rising).check 19 10 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_10_5_checked :
    (Witness.rising).check 19 10 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_10_6 : Certificate := {
  objectiveScale := 16800000
  eta := 352800000
  rows := #[⟨.count 2, 86553600⟩, ⟨.count 3, 36300600⟩, ⟨.count 4, 22352400⟩, ⟨.count 5, 20386800⟩, ⟨.count 7, 16787400⟩, ⟨.path 6, 8399880⟩, ⟨.privateRow 4 3, 1400175⟩, ⟨.privateRow 5 1, 1959888⟩, ⟨.privateRow 6 0, 1457820⟩, ⟨.hall 4 4, 168280⟩, ⟨.hall 3 5, 930900⟩, ⟨.hall 2 7, 5832225⟩, ⟨.assumptionRow 6, 22350600⟩]
  caps := #[0, 0, 0, 1170, 0, 3912, 3780, 12600, 0, 0] }

theorem case_19_10_6_checked :
    (Witness.linear .conditional case_19_10_6).check 19 10 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_11_1_checked :
    (Witness.rising).check 19 11 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_11_2_checked :
    (Witness.rising).check 19 11 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_11_3_checked :
    (Witness.rising).check 19 11 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_11_4_checked :
    (Witness.rising).check 19 11 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_11_5_checked :
    (Witness.rising).check 19 11 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_11_6 : Certificate := {
  objectiveScale := 435600000
  eta := 12966723000
  rows := #[⟨.count 2, 3523350600⟩, ⟨.count 3, 1301246100⟩, ⟨.count 4, 744614640⟩, ⟨.count 5, 625086000⟩, ⟨.path 5, 248102400⟩, ⟨.privateRow 3 6, 156271500⟩, ⟨.privateRow 4 3, 25369344⟩, ⟨.privateRow 4 4, 142283295⟩, ⟨.privateRow 5 1, 59561040⟩, ⟨.privateRow 5 2, 35370720⟩, ⟨.privateRow 6 0, 68310550⟩, ⟨.privateRow 7 0, 87054660⟩, ⟨.hall 2 8, 78940400⟩, ⟨.assumptionRow 6, 496202850⟩]
  caps := #[0, 0, 81900, 0, 0, 619890, 0, 326700, 0] }

theorem case_19_11_6_checked :
    (Witness.linear .conditional case_19_11_6).check 19 11 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_12_1_checked :
    (Witness.rising).check 19 12 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_12_2_checked :
    (Witness.rising).check 19 12 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_12_3_checked :
    (Witness.rising).check 19 12 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_12_4_checked :
    (Witness.rising).check 19 12 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_12_5_checked :
    (Witness.rising).check 19 12 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_12_6 : Certificate := {
  objectiveScale := 40000
  eta := 2519640
  rows := #[⟨.count 2, 699840⟩, ⟨.count 3, 200016⟩, ⟨.count 4, 79920⟩, ⟨.count 5, 60120⟩, ⟨.path 5, 20001⟩]
  caps := #[0, 570, 195, 0, 82, 0, 0, 0] }

theorem case_19_12_6_checked :
    (Witness.linear .positive case_19_12_6).check 19 12 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_12_7 : Certificate := {
  objectiveScale := 483000000
  eta := 14357851200
  rows := #[⟨.count 3, 564878160⟩, ⟨.count 7, 1919055600⟩, ⟨.path 3, 565432560⟩, ⟨.privateRow 2 5, 429998800⟩, ⟨.privateRow 2 6, 37403520⟩, ⟨.privateRow 2 8, 1032847200⟩, ⟨.privateRow 2 9, 985561500⟩, ⟨.privateRow 3 4, 77003080⟩, ⟨.privateRow 3 5, 496361712⟩, ⟨.privateRow 3 6, 482951700⟩, ⟨.privateRow 3 7, 229379920⟩, ⟨.privateRow 4 1, 38492685⟩, ⟨.privateRow 4 2, 98184240⟩, ⟨.privateRow 4 3, 296677920⟩, ⟨.privateRow 4 4, 150974208⟩, ⟨.privateRow 5 0, 233506350⟩, ⟨.privateRow 6 0, 117493200⟩]
  caps := #[0, 4989600, 0, 1305304, 0, 676200, 0, 12944400] }

theorem case_19_12_7_checked :
    (Witness.linear .negative case_19_12_7).check 19 12 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_13_1_checked :
    (Witness.rising).check 19 13 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_13_2_checked :
    (Witness.rising).check 19 13 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_13_3_checked :
    (Witness.rising).check 19 13 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_13_4_checked :
    (Witness.rising).check 19 13 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_13_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0, 2, 1, 1, 0, 0] }

theorem case_19_13_5_checked :
    (Witness.linear .positive case_19_13_5).check 19 13 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_13_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1, 1, 0] }

theorem case_19_13_6_checked :
    (Witness.linear .positive case_19_13_6).check 19 13 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_13_7 : Certificate := {
  objectiveScale := 7
  eta := 42
  rows := #[⟨.assumptionRow 7, 6⟩]
  caps := #[0, 0, 19, 11, 6, 76, 62] }

theorem case_19_13_7_checked :
    (Witness.linear .conditional case_19_13_7).check 19 13 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_13_8 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 14, 14] }

theorem case_19_13_8_checked :
    (Witness.linear .negative case_19_13_8).check 19 13 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_14_1_checked :
    (Witness.rising).check 19 14 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_14_2_checked :
    (Witness.rising).check 19 14 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_14_3_checked :
    (Witness.rising).check 19 14 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_14_4_checked :
    (Witness.rising).check 19 14 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_14_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0, 2, 1, 1, 0] }

theorem case_19_14_5_checked :
    (Witness.linear .positive case_19_14_5).check 19 14 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_14_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1, 1] }

theorem case_19_14_6_checked :
    (Witness.linear .positive case_19_14_6).check 19 14 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_14_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1] }

theorem case_19_14_7_checked :
    (Witness.linear .positive case_19_14_7).check 19 14 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_14_8 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 42, 42] }

theorem case_19_14_8_checked :
    (Witness.linear .negative case_19_14_8).check 19 14 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_15_1_checked :
    (Witness.rising).check 19 15 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_15_2_checked :
    (Witness.rising).check 19 15 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_15_3_checked :
    (Witness.rising).check 19 15 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_15_4_checked :
    (Witness.rising).check 19 15 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_15_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0, 2, 1, 1] }

theorem case_19_15_5_checked :
    (Witness.linear .positive case_19_15_5).check 19 15 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_15_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1] }

theorem case_19_15_6_checked :
    (Witness.linear .positive case_19_15_6).check 19 15 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_15_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2] }

theorem case_19_15_7_checked :
    (Witness.linear .positive case_19_15_7).check 19 15 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_15_8 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 132, 132] }

theorem case_19_15_8_checked :
    (Witness.linear .negative case_19_15_8).check 19 15 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_15_9 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_19_15_9_checked :
    (Witness.linear .negative case_19_15_9).check 19 15 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_16_1_checked :
    (Witness.rising).check 19 16 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_16_2_checked :
    (Witness.rising).check 19 16 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_16_3_checked :
    (Witness.rising).check 19 16 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_16_4_checked :
    (Witness.rising).check 19 16 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_16_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0, 2, 1] }

theorem case_19_16_5_checked :
    (Witness.linear .positive case_19_16_5).check 19 16 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_16_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2] }

theorem case_19_16_6_checked :
    (Witness.linear .positive case_19_16_6).check 19 16 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_16_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5] }

theorem case_19_16_7_checked :
    (Witness.linear .positive case_19_16_7).check 19 16 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_16_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14] }

theorem case_19_16_8_checked :
    (Witness.linear .positive case_19_16_8).check 19 16 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_16_9 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_19_16_9_checked :
    (Witness.linear .negative case_19_16_9).check 19 16 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_16_10 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_19_16_10_checked :
    (Witness.linear .negative case_19_16_10).check 19 16 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_17_1_checked :
    (Witness.rising).check 19 17 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_17_2_checked :
    (Witness.rising).check 19 17 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_17_3_checked :
    (Witness.rising).check 19 17 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_17_4_checked :
    (Witness.rising).check 19 17 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_17_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0, 2] }

theorem case_19_17_5_checked :
    (Witness.linear .positive case_19_17_5).check 19 17 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_17_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5] }

theorem case_19_17_6_checked :
    (Witness.linear .positive case_19_17_6).check 19 17 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_17_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14] }

theorem case_19_17_7_checked :
    (Witness.linear .positive case_19_17_7).check 19 17 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_17_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42] }

theorem case_19_17_8_checked :
    (Witness.linear .positive case_19_17_8).check 19 17 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_17_9 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_19_17_9_checked :
    (Witness.linear .negative case_19_17_9).check 19 17 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_17_10 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_19_17_10_checked :
    (Witness.linear .negative case_19_17_10).check 19 17 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_18_1_checked :
    (Witness.rising).check 19 18 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_18_2_checked :
    (Witness.rising).check 19 18 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_18_3_checked :
    (Witness.rising).check 19 18 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_19_18_4_checked :
    (Witness.rising).check 19 18 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_18_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0] }

theorem case_19_18_5_checked :
    (Witness.linear .positive case_19_18_5).check 19 18 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_18_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0] }

theorem case_19_18_6_checked :
    (Witness.linear .positive case_19_18_6).check 19 18 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_18_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0] }

theorem case_19_18_7_checked :
    (Witness.linear .positive case_19_18_7).check 19 18 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_18_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0] }

theorem case_19_18_8_checked :
    (Witness.linear .positive case_19_18_8).check 19 18 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_18_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_19_18_9_checked :
    (Witness.linear .positive case_19_18_9).check 19 18 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_18_10 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_19_18_10_checked :
    (Witness.linear .negative case_19_18_10).check 19 18 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_19_18_11 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_19_18_11_checked :
    (Witness.linear .negative case_19_18_11).check 19 18 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_19 (a k : ℕ) (h : Domain 19 a k) :
    ∃ w : Witness, w.check 19 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 10 ≤ a := by omega
  have haHi : a ≤ 18 := by omega
  interval_cases a

  · have hkHi : k ≤ 6 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_19_10_1_checked⟩

    · exact ⟨Witness.rising, case_19_10_2_checked⟩

    · exact ⟨Witness.rising, case_19_10_3_checked⟩

    · exact ⟨Witness.rising, case_19_10_4_checked⟩

    · exact ⟨Witness.rising, case_19_10_5_checked⟩

    · exact ⟨Witness.linear .conditional case_19_10_6, case_19_10_6_checked⟩

  · have hkHi : k ≤ 6 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_19_11_1_checked⟩

    · exact ⟨Witness.rising, case_19_11_2_checked⟩

    · exact ⟨Witness.rising, case_19_11_3_checked⟩

    · exact ⟨Witness.rising, case_19_11_4_checked⟩

    · exact ⟨Witness.rising, case_19_11_5_checked⟩

    · exact ⟨Witness.linear .conditional case_19_11_6, case_19_11_6_checked⟩

  · have hkHi : k ≤ 7 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_19_12_1_checked⟩

    · exact ⟨Witness.rising, case_19_12_2_checked⟩

    · exact ⟨Witness.rising, case_19_12_3_checked⟩

    · exact ⟨Witness.rising, case_19_12_4_checked⟩

    · exact ⟨Witness.rising, case_19_12_5_checked⟩

    · exact ⟨Witness.linear .positive case_19_12_6, case_19_12_6_checked⟩

    · exact ⟨Witness.linear .negative case_19_12_7, case_19_12_7_checked⟩

  · have hkHi : k ≤ 8 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_19_13_1_checked⟩

    · exact ⟨Witness.rising, case_19_13_2_checked⟩

    · exact ⟨Witness.rising, case_19_13_3_checked⟩

    · exact ⟨Witness.rising, case_19_13_4_checked⟩

    · exact ⟨Witness.linear .positive case_19_13_5, case_19_13_5_checked⟩

    · exact ⟨Witness.linear .positive case_19_13_6, case_19_13_6_checked⟩

    · exact ⟨Witness.linear .conditional case_19_13_7, case_19_13_7_checked⟩

    · exact ⟨Witness.linear .negative case_19_13_8, case_19_13_8_checked⟩

  · have hkHi : k ≤ 8 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_19_14_1_checked⟩

    · exact ⟨Witness.rising, case_19_14_2_checked⟩

    · exact ⟨Witness.rising, case_19_14_3_checked⟩

    · exact ⟨Witness.rising, case_19_14_4_checked⟩

    · exact ⟨Witness.linear .positive case_19_14_5, case_19_14_5_checked⟩

    · exact ⟨Witness.linear .positive case_19_14_6, case_19_14_6_checked⟩

    · exact ⟨Witness.linear .positive case_19_14_7, case_19_14_7_checked⟩

    · exact ⟨Witness.linear .negative case_19_14_8, case_19_14_8_checked⟩

  · have hkHi : k ≤ 9 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_19_15_1_checked⟩

    · exact ⟨Witness.rising, case_19_15_2_checked⟩

    · exact ⟨Witness.rising, case_19_15_3_checked⟩

    · exact ⟨Witness.rising, case_19_15_4_checked⟩

    · exact ⟨Witness.linear .positive case_19_15_5, case_19_15_5_checked⟩

    · exact ⟨Witness.linear .positive case_19_15_6, case_19_15_6_checked⟩

    · exact ⟨Witness.linear .positive case_19_15_7, case_19_15_7_checked⟩

    · exact ⟨Witness.linear .negative case_19_15_8, case_19_15_8_checked⟩

    · exact ⟨Witness.linear .negative case_19_15_9, case_19_15_9_checked⟩

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_19_16_1_checked⟩

    · exact ⟨Witness.rising, case_19_16_2_checked⟩

    · exact ⟨Witness.rising, case_19_16_3_checked⟩

    · exact ⟨Witness.rising, case_19_16_4_checked⟩

    · exact ⟨Witness.linear .positive case_19_16_5, case_19_16_5_checked⟩

    · exact ⟨Witness.linear .positive case_19_16_6, case_19_16_6_checked⟩

    · exact ⟨Witness.linear .positive case_19_16_7, case_19_16_7_checked⟩

    · exact ⟨Witness.linear .positive case_19_16_8, case_19_16_8_checked⟩

    · exact ⟨Witness.linear .negative case_19_16_9, case_19_16_9_checked⟩

    · exact ⟨Witness.linear .negative case_19_16_10, case_19_16_10_checked⟩

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_19_17_1_checked⟩

    · exact ⟨Witness.rising, case_19_17_2_checked⟩

    · exact ⟨Witness.rising, case_19_17_3_checked⟩

    · exact ⟨Witness.rising, case_19_17_4_checked⟩

    · exact ⟨Witness.linear .positive case_19_17_5, case_19_17_5_checked⟩

    · exact ⟨Witness.linear .positive case_19_17_6, case_19_17_6_checked⟩

    · exact ⟨Witness.linear .positive case_19_17_7, case_19_17_7_checked⟩

    · exact ⟨Witness.linear .positive case_19_17_8, case_19_17_8_checked⟩

    · exact ⟨Witness.linear .negative case_19_17_9, case_19_17_9_checked⟩

    · exact ⟨Witness.linear .negative case_19_17_10, case_19_17_10_checked⟩

  · have hkHi : k ≤ 11 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_19_18_1_checked⟩

    · exact ⟨Witness.rising, case_19_18_2_checked⟩

    · exact ⟨Witness.rising, case_19_18_3_checked⟩

    · exact ⟨Witness.rising, case_19_18_4_checked⟩

    · exact ⟨Witness.linear .positive case_19_18_5, case_19_18_5_checked⟩

    · exact ⟨Witness.linear .positive case_19_18_6, case_19_18_6_checked⟩

    · exact ⟨Witness.linear .positive case_19_18_7, case_19_18_7_checked⟩

    · exact ⟨Witness.linear .positive case_19_18_8, case_19_18_8_checked⟩

    · exact ⟨Witness.linear .positive case_19_18_9, case_19_18_9_checked⟩

    · exact ⟨Witness.linear .negative case_19_18_10, case_19_18_10_checked⟩

    · exact ⟨Witness.linear .negative case_19_18_11, case_19_18_11_checked⟩


#print axioms coverage_19
end ForestUnimodality.FiniteRows.FiniteData
