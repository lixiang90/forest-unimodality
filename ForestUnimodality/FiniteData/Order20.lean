import ForestUnimodality.FiniteWitness
import Mathlib.Tactic.IntervalCases

/-! Generated candidate witnesses. Each sign is rechecked by the Lean kernel.
The coverage theorem quantifies over Domain, independently of this record list.
Source and integer-witness hashes are recorded in research/finite-integer-witnesses/manifest.json.
-/
namespace ForestUnimodality.FiniteRows.FiniteData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_20_10_1_checked :
    (Witness.rising).check 20 10 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_10_2_checked :
    (Witness.rising).check 20 10 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_10_3_checked :
    (Witness.rising).check 20 10 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_10_4_checked :
    (Witness.rising).check 20 10 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_10_5_checked :
    (Witness.rising).check 20 10 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_10_6 : Certificate := {
  objectiveScale := 164400000
  eta := 4312738080
  rows := #[⟨.count 2, 2171789760⟩, ⟨.count 3, 657164340⟩, ⟨.count 4, 319494960⟩, ⟨.count 5, 313428600⟩, ⟨.path 6, 127815840⟩, ⟨.privateRow 5 1, 6095952⟩, ⟨.privateRow 7 0, 41102055⟩, ⟨.hall 5 1, 25124430⟩, ⟨.hall 5 2, 9891400⟩, ⟨.hall 4 3, 10812588⟩, ⟨.hall 0 4, 38781960⟩, ⟨.hall 3 5, 15646770⟩, ⟨.assumptionRow 6, 319538800⟩]
  caps := #[0, 730800, 175840, 11200, 43840, 81608, 33200, 0, 0, 0, 0] }

theorem case_20_10_6_checked :
    (Witness.linear .conditional case_20_10_6).check 20 10 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_11_1_checked :
    (Witness.rising).check 20 11 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_11_2_checked :
    (Witness.rising).check 20 11 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_11_3_checked :
    (Witness.rising).check 20 11 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_11_4_checked :
    (Witness.rising).check 20 11 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_11_5_checked :
    (Witness.rising).check 20 11 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_11_6 : Certificate := {
  objectiveScale := 37500
  eta := 2205000
  rows := #[⟨.count 2, 525035⟩, ⟨.count 3, 150045⟩, ⟨.count 4, 52500⟩, ⟨.count 5, 37520⟩, ⟨.path 6, 15000⟩, ⟨.privateRow 7 0, 2814⟩, ⟨.hall 5 3, 469⟩]
  caps := #[0, 0, 0, 0, 0, 0, 12, 0, 0, 0] }

theorem case_20_11_6_checked :
    (Witness.linear .positive case_20_11_6).check 20 11 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_12_1_checked :
    (Witness.rising).check 20 12 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_12_2_checked :
    (Witness.rising).check 20 12 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_12_3_checked :
    (Witness.rising).check 20 12 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_12_4_checked :
    (Witness.rising).check 20 12 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_12_5_checked :
    (Witness.rising).check 20 12 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_12_6 : Certificate := {
  objectiveScale := 625
  eta := 36750
  rows := #[⟨.count 2, 8748⟩, ⟨.count 3, 2499⟩, ⟨.count 4, 876⟩, ⟨.count 5, 624⟩, ⟨.path 6, 250⟩]
  caps := #[0, 0, 2, 1, 0, 1, 0, 0, 0] }

theorem case_20_12_6_checked :
    (Witness.linear .positive case_20_12_6).check 20 12 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_12_7 : Certificate := {
  objectiveScale := 565500000
  eta := 38230797150
  rows := #[⟨.count 2, 9255764700⟩, ⟨.count 3, 2784804750⟩, ⟨.count 4, 896837760⟩, ⟨.count 5, 5937750⟩, ⟨.count 8, 598525200⟩, ⟨.path 4, 659736000⟩, ⟨.privateRow 2 10, 573586650⟩, ⟨.privateRow 3 7, 549835650⟩, ⟨.privateRow 3 8, 329347200⟩, ⟨.privateRow 4 4, 112532238⟩, ⟨.privateRow 4 5, 430961895⟩, ⟨.privateRow 4 6, 35626500⟩, ⟨.privateRow 5 2, 138389160⟩, ⟨.privateRow 5 3, 173619810⟩, ⟨.privateRow 6 0, 15381600⟩, ⟨.privateRow 6 1, 129376975⟩, ⟨.privateRow 7 0, 56210700⟩, ⟨.assumptionRow 7, 237029325⟩]
  caps := #[0, 0, 1745100, 0, 621999, 458055, 0, 1385475, 0] }

theorem case_20_12_7_checked :
    (Witness.linear .conditional case_20_12_7).check 20 12 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_13_1_checked :
    (Witness.rising).check 20 13 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_13_2_checked :
    (Witness.rising).check 20 13 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_13_3_checked :
    (Witness.rising).check 20 13 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_13_4_checked :
    (Witness.rising).check 20 13 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_13_5_checked :
    (Witness.rising).check 20 13 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_13_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1, 1, 0, 0] }

theorem case_20_13_6_checked :
    (Witness.linear .positive case_20_13_6).check 20 13 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_13_7 : Certificate := {
  objectiveScale := 8880000
  eta := 1116269280
  rows := #[⟨.count 2, 250629120⟩, ⟨.count 3, 64522080⟩, ⟨.count 4, 19841472⟩, ⟨.count 5, 2797200⟩, ⟨.path 4, 13868960⟩, ⟨.privateRow 2 11, 4413360⟩, ⟨.privateRow 3 7, 5448324⟩, ⟨.privateRow 3 8, 11507888⟩, ⟨.privateRow 4 4, 203574⟩, ⟨.privateRow 4 5, 10153836⟩, ⟨.privateRow 4 6, 1135197⟩, ⟨.privateRow 5 2, 1170384⟩, ⟨.privateRow 5 3, 4838120⟩, ⟨.privateRow 6 0, 151515⟩, ⟨.privateRow 6 1, 2384280⟩, ⟨.privateRow 7 0, 905760⟩, ⟨.assumptionRow 7, 5979792⟩]
  caps := #[0, 0, 20468, 33432, 7502, 0, 48063, 0] }

theorem case_20_13_7_checked :
    (Witness.linear .conditional case_20_13_7).check 20 13 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_13_8 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 14, 14, 9] }

theorem case_20_13_8_checked :
    (Witness.linear .negative case_20_13_8).check 20 13 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_14_1_checked :
    (Witness.rising).check 20 14 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_14_2_checked :
    (Witness.rising).check 20 14 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_14_3_checked :
    (Witness.rising).check 20 14 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_14_4_checked :
    (Witness.rising).check 20 14 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_14_5_checked :
    (Witness.rising).check 20 14 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_14_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1, 1, 0] }

theorem case_20_14_6_checked :
    (Witness.linear .positive case_20_14_6).check 20 14 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_14_7 : Certificate := {
  objectiveScale := 7
  eta := 196
  rows := #[⟨.assumptionRow 7, 12⟩]
  caps := #[0, 0, 73, 32, 17, 12, 56] }

theorem case_20_14_7_checked :
    (Witness.linear .conditional case_20_14_7).check 20 14 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_14_8 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 42, 42, 28] }

theorem case_20_14_8_checked :
    (Witness.linear .negative case_20_14_8).check 20 14 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_15_1_checked :
    (Witness.rising).check 20 15 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_15_2_checked :
    (Witness.rising).check 20 15 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_15_3_checked :
    (Witness.rising).check 20 15 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_15_4_checked :
    (Witness.rising).check 20 15 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_15_5_checked :
    (Witness.rising).check 20 15 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_15_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1, 1] }

theorem case_20_15_6_checked :
    (Witness.linear .positive case_20_15_6).check 20 15 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_15_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1] }

theorem case_20_15_7_checked :
    (Witness.linear .positive case_20_15_7).check 20 15 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_15_8 : Certificate := {
  objectiveScale := 24
  eta := 264
  rows := #[⟨.assumptionRow 8, 19⟩]
  caps := #[0, 0, 122, 52, 33, 735] }

theorem case_20_15_8_checked :
    (Witness.linear .conditional case_20_15_8).check 20 15 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_15_9 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 42] }

theorem case_20_15_9_checked :
    (Witness.linear .negative case_20_15_9).check 20 15 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_16_1_checked :
    (Witness.rising).check 20 16 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_16_2_checked :
    (Witness.rising).check 20 16 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_16_3_checked :
    (Witness.rising).check 20 16 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_16_4_checked :
    (Witness.rising).check 20 16 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_16_5_checked :
    (Witness.rising).check 20 16 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_16_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1] }

theorem case_20_16_6_checked :
    (Witness.linear .positive case_20_16_6).check 20 16 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_16_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2] }

theorem case_20_16_7_checked :
    (Witness.linear .positive case_20_16_7).check 20 16 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_16_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5] }

theorem case_20_16_8_checked :
    (Witness.linear .positive case_20_16_8).check 20 16 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_16_9 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 132] }

theorem case_20_16_9_checked :
    (Witness.linear .negative case_20_16_9).check 20 16 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_16_10 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_20_16_10_checked :
    (Witness.linear .negative case_20_16_10).check 20 16 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_17_1_checked :
    (Witness.rising).check 20 17 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_17_2_checked :
    (Witness.rising).check 20 17 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_17_3_checked :
    (Witness.rising).check 20 17 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_17_4_checked :
    (Witness.rising).check 20 17 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_17_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0, 2, 1] }

theorem case_20_17_5_checked :
    (Witness.linear .positive case_20_17_5).check 20 17 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_17_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2] }

theorem case_20_17_6_checked :
    (Witness.linear .positive case_20_17_6).check 20 17 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_17_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5] }

theorem case_20_17_7_checked :
    (Witness.linear .positive case_20_17_7).check 20 17 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_17_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14] }

theorem case_20_17_8_checked :
    (Witness.linear .positive case_20_17_8).check 20 17 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_17_9 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 429] }

theorem case_20_17_9_checked :
    (Witness.linear .negative case_20_17_9).check 20 17 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_17_10 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_20_17_10_checked :
    (Witness.linear .negative case_20_17_10).check 20 17 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_18_1_checked :
    (Witness.rising).check 20 18 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_18_2_checked :
    (Witness.rising).check 20 18 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_18_3_checked :
    (Witness.rising).check 20 18 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_18_4_checked :
    (Witness.rising).check 20 18 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_18_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0, 2] }

theorem case_20_18_5_checked :
    (Witness.linear .positive case_20_18_5).check 20 18 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_18_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5] }

theorem case_20_18_6_checked :
    (Witness.linear .positive case_20_18_6).check 20 18 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_18_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14] }

theorem case_20_18_7_checked :
    (Witness.linear .positive case_20_18_7).check 20 18 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_18_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42] }

theorem case_20_18_8_checked :
    (Witness.linear .positive case_20_18_8).check 20 18 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_18_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_20_18_9_checked :
    (Witness.linear .positive case_20_18_9).check 20 18 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_18_10 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_20_18_10_checked :
    (Witness.linear .negative case_20_18_10).check 20 18 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_18_11 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_20_18_11_checked :
    (Witness.linear .negative case_20_18_11).check 20 18 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_19_1_checked :
    (Witness.rising).check 20 19 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_19_2_checked :
    (Witness.rising).check 20 19 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_19_3_checked :
    (Witness.rising).check 20 19 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_20_19_4_checked :
    (Witness.rising).check 20 19 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_19_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0] }

theorem case_20_19_5_checked :
    (Witness.linear .positive case_20_19_5).check 20 19 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_19_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0] }

theorem case_20_19_6_checked :
    (Witness.linear .positive case_20_19_6).check 20 19 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_19_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0] }

theorem case_20_19_7_checked :
    (Witness.linear .positive case_20_19_7).check 20 19 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_19_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0] }

theorem case_20_19_8_checked :
    (Witness.linear .positive case_20_19_8).check 20 19 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_19_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_20_19_9_checked :
    (Witness.linear .positive case_20_19_9).check 20 19 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_19_10 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_20_19_10_checked :
    (Witness.linear .negative case_20_19_10).check 20 19 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_19_11 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_20_19_11_checked :
    (Witness.linear .negative case_20_19_11).check 20 19 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_20_19_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_20_19_12_checked :
    (Witness.linear .negative case_20_19_12).check 20 19 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_20 (a k : ℕ) (h : Domain 20 a k) :
    ∃ w : Witness, w.check 20 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 10 ≤ a := by omega
  have haHi : a ≤ 19 := by omega
  interval_cases a

  · have hkHi : k ≤ 6 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_20_10_1_checked⟩

    · exact ⟨Witness.rising, case_20_10_2_checked⟩

    · exact ⟨Witness.rising, case_20_10_3_checked⟩

    · exact ⟨Witness.rising, case_20_10_4_checked⟩

    · exact ⟨Witness.rising, case_20_10_5_checked⟩

    · exact ⟨Witness.linear .conditional case_20_10_6, case_20_10_6_checked⟩

  · have hkHi : k ≤ 6 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_20_11_1_checked⟩

    · exact ⟨Witness.rising, case_20_11_2_checked⟩

    · exact ⟨Witness.rising, case_20_11_3_checked⟩

    · exact ⟨Witness.rising, case_20_11_4_checked⟩

    · exact ⟨Witness.rising, case_20_11_5_checked⟩

    · exact ⟨Witness.linear .positive case_20_11_6, case_20_11_6_checked⟩

  · have hkHi : k ≤ 7 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_20_12_1_checked⟩

    · exact ⟨Witness.rising, case_20_12_2_checked⟩

    · exact ⟨Witness.rising, case_20_12_3_checked⟩

    · exact ⟨Witness.rising, case_20_12_4_checked⟩

    · exact ⟨Witness.rising, case_20_12_5_checked⟩

    · exact ⟨Witness.linear .positive case_20_12_6, case_20_12_6_checked⟩

    · exact ⟨Witness.linear .conditional case_20_12_7, case_20_12_7_checked⟩

  · have hkHi : k ≤ 8 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_20_13_1_checked⟩

    · exact ⟨Witness.rising, case_20_13_2_checked⟩

    · exact ⟨Witness.rising, case_20_13_3_checked⟩

    · exact ⟨Witness.rising, case_20_13_4_checked⟩

    · exact ⟨Witness.rising, case_20_13_5_checked⟩

    · exact ⟨Witness.linear .positive case_20_13_6, case_20_13_6_checked⟩

    · exact ⟨Witness.linear .conditional case_20_13_7, case_20_13_7_checked⟩

    · exact ⟨Witness.linear .negative case_20_13_8, case_20_13_8_checked⟩

  · have hkHi : k ≤ 8 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_20_14_1_checked⟩

    · exact ⟨Witness.rising, case_20_14_2_checked⟩

    · exact ⟨Witness.rising, case_20_14_3_checked⟩

    · exact ⟨Witness.rising, case_20_14_4_checked⟩

    · exact ⟨Witness.rising, case_20_14_5_checked⟩

    · exact ⟨Witness.linear .positive case_20_14_6, case_20_14_6_checked⟩

    · exact ⟨Witness.linear .conditional case_20_14_7, case_20_14_7_checked⟩

    · exact ⟨Witness.linear .negative case_20_14_8, case_20_14_8_checked⟩

  · have hkHi : k ≤ 9 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_20_15_1_checked⟩

    · exact ⟨Witness.rising, case_20_15_2_checked⟩

    · exact ⟨Witness.rising, case_20_15_3_checked⟩

    · exact ⟨Witness.rising, case_20_15_4_checked⟩

    · exact ⟨Witness.rising, case_20_15_5_checked⟩

    · exact ⟨Witness.linear .positive case_20_15_6, case_20_15_6_checked⟩

    · exact ⟨Witness.linear .positive case_20_15_7, case_20_15_7_checked⟩

    · exact ⟨Witness.linear .conditional case_20_15_8, case_20_15_8_checked⟩

    · exact ⟨Witness.linear .negative case_20_15_9, case_20_15_9_checked⟩

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_20_16_1_checked⟩

    · exact ⟨Witness.rising, case_20_16_2_checked⟩

    · exact ⟨Witness.rising, case_20_16_3_checked⟩

    · exact ⟨Witness.rising, case_20_16_4_checked⟩

    · exact ⟨Witness.rising, case_20_16_5_checked⟩

    · exact ⟨Witness.linear .positive case_20_16_6, case_20_16_6_checked⟩

    · exact ⟨Witness.linear .positive case_20_16_7, case_20_16_7_checked⟩

    · exact ⟨Witness.linear .positive case_20_16_8, case_20_16_8_checked⟩

    · exact ⟨Witness.linear .negative case_20_16_9, case_20_16_9_checked⟩

    · exact ⟨Witness.linear .negative case_20_16_10, case_20_16_10_checked⟩

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_20_17_1_checked⟩

    · exact ⟨Witness.rising, case_20_17_2_checked⟩

    · exact ⟨Witness.rising, case_20_17_3_checked⟩

    · exact ⟨Witness.rising, case_20_17_4_checked⟩

    · exact ⟨Witness.linear .positive case_20_17_5, case_20_17_5_checked⟩

    · exact ⟨Witness.linear .positive case_20_17_6, case_20_17_6_checked⟩

    · exact ⟨Witness.linear .positive case_20_17_7, case_20_17_7_checked⟩

    · exact ⟨Witness.linear .positive case_20_17_8, case_20_17_8_checked⟩

    · exact ⟨Witness.linear .negative case_20_17_9, case_20_17_9_checked⟩

    · exact ⟨Witness.linear .negative case_20_17_10, case_20_17_10_checked⟩

  · have hkHi : k ≤ 11 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_20_18_1_checked⟩

    · exact ⟨Witness.rising, case_20_18_2_checked⟩

    · exact ⟨Witness.rising, case_20_18_3_checked⟩

    · exact ⟨Witness.rising, case_20_18_4_checked⟩

    · exact ⟨Witness.linear .positive case_20_18_5, case_20_18_5_checked⟩

    · exact ⟨Witness.linear .positive case_20_18_6, case_20_18_6_checked⟩

    · exact ⟨Witness.linear .positive case_20_18_7, case_20_18_7_checked⟩

    · exact ⟨Witness.linear .positive case_20_18_8, case_20_18_8_checked⟩

    · exact ⟨Witness.linear .positive case_20_18_9, case_20_18_9_checked⟩

    · exact ⟨Witness.linear .negative case_20_18_10, case_20_18_10_checked⟩

    · exact ⟨Witness.linear .negative case_20_18_11, case_20_18_11_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_20_19_1_checked⟩

    · exact ⟨Witness.rising, case_20_19_2_checked⟩

    · exact ⟨Witness.rising, case_20_19_3_checked⟩

    · exact ⟨Witness.rising, case_20_19_4_checked⟩

    · exact ⟨Witness.linear .positive case_20_19_5, case_20_19_5_checked⟩

    · exact ⟨Witness.linear .positive case_20_19_6, case_20_19_6_checked⟩

    · exact ⟨Witness.linear .positive case_20_19_7, case_20_19_7_checked⟩

    · exact ⟨Witness.linear .positive case_20_19_8, case_20_19_8_checked⟩

    · exact ⟨Witness.linear .positive case_20_19_9, case_20_19_9_checked⟩

    · exact ⟨Witness.linear .negative case_20_19_10, case_20_19_10_checked⟩

    · exact ⟨Witness.linear .negative case_20_19_11, case_20_19_11_checked⟩

    · exact ⟨Witness.linear .negative case_20_19_12, case_20_19_12_checked⟩


#print axioms coverage_20
end ForestUnimodality.FiniteRows.FiniteData
