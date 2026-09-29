import ForestUnimodality.FiniteWitness
import Mathlib.Tactic.IntervalCases

/-! Generated candidate witnesses. Each sign is rechecked by the Lean kernel.
The coverage theorem quantifies over Domain, independently of this record list.
Source and integer-witness hashes are recorded in research/finite-integer-witnesses/manifest.json.
-/
namespace ForestUnimodality.FiniteRows.FiniteData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_16_8_1_checked :
    (Witness.rising).check 16 8 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_8_2_checked :
    (Witness.rising).check 16 8 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_8_3_checked :
    (Witness.rising).check 16 8 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_8_4_checked :
    (Witness.rising).check 16 8 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_9_1_checked :
    (Witness.rising).check 16 9 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_9_2_checked :
    (Witness.rising).check 16 9 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_9_3_checked :
    (Witness.rising).check 16 9 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_9_4_checked :
    (Witness.rising).check 16 9 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_16_9_5 : Certificate := {
  objectiveScale := 70000
  eta := 979965
  rows := #[⟨.count 2, 280035⟩, ⟨.count 3, 98028⟩, ⟨.count 4, 69993⟩, ⟨.path 5, 27999⟩]
  caps := #[0, 0, 0, 0, 7, 0, 0, 0] }

theorem case_16_9_5_checked :
    (Witness.linear .positive case_16_9_5).check 16 9 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_10_1_checked :
    (Witness.rising).check 16 10 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_10_2_checked :
    (Witness.rising).check 16 10 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_10_3_checked :
    (Witness.rising).check 16 10 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_10_4_checked :
    (Witness.rising).check 16 10 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_16_10_5 : Certificate := {
  objectiveScale := 10000
  eta := 140000
  rows := #[⟨.count 2, 40012⟩, ⟨.count 3, 14007⟩, ⟨.count 4, 9996⟩, ⟨.path 5, 4000⟩]
  caps := #[0, 0, 0, 0, 4, 0, 0] }

theorem case_16_10_5_checked :
    (Witness.linear .positive case_16_10_5).check 16 10 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_16_10_6 : Certificate := {
  objectiveScale := 2
  eta := 2
  rows := #[⟨.assumptionRow 6, 1⟩]
  caps := #[0, 0, 1, 1, 1, 6, 5] }

theorem case_16_10_6_checked :
    (Witness.linear .conditional case_16_10_6).check 16 10 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_11_1_checked :
    (Witness.rising).check 16 11 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_11_2_checked :
    (Witness.rising).check 16 11 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_11_3_checked :
    (Witness.rising).check 16 11 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_11_4_checked :
    (Witness.rising).check 16 11 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_16_11_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0, 2, 1, 1, 0] }

theorem case_16_11_5_checked :
    (Witness.linear .positive case_16_11_5).check 16 11 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_16_11_6 : Certificate := {
  objectiveScale := 5
  eta := 11
  rows := #[⟨.assumptionRow 6, 4⟩]
  caps := #[0, 0, 7, 4, 14, 25] }

theorem case_16_11_6_checked :
    (Witness.linear .conditional case_16_11_6).check 16 11 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_12_1_checked :
    (Witness.rising).check 16 12 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_12_2_checked :
    (Witness.rising).check 16 12 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_12_3_checked :
    (Witness.rising).check 16 12 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_12_4_checked :
    (Witness.rising).check 16 12 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_16_12_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0, 2, 1, 1] }

theorem case_16_12_5_checked :
    (Witness.linear .positive case_16_12_5).check 16 12 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_16_12_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1] }

theorem case_16_12_6_checked :
    (Witness.linear .positive case_16_12_6).check 16 12 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_16_12_7 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 14] }

theorem case_16_12_7_checked :
    (Witness.linear .negative case_16_12_7).check 16 12 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_13_1_checked :
    (Witness.rising).check 16 13 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_13_2_checked :
    (Witness.rising).check 16 13 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_13_3_checked :
    (Witness.rising).check 16 13 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_13_4_checked :
    (Witness.rising).check 16 13 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_16_13_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0, 2, 1] }

theorem case_16_13_5_checked :
    (Witness.linear .positive case_16_13_5).check 16 13 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_16_13_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2] }

theorem case_16_13_6_checked :
    (Witness.linear .positive case_16_13_6).check 16 13 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_16_13_7 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 42] }

theorem case_16_13_7_checked :
    (Witness.linear .negative case_16_13_7).check 16 13 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_16_13_8 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_16_13_8_checked :
    (Witness.linear .negative case_16_13_8).check 16 13 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_14_1_checked :
    (Witness.rising).check 16 14 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_14_2_checked :
    (Witness.rising).check 16 14 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_14_3_checked :
    (Witness.rising).check 16 14 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_14_4_checked :
    (Witness.rising).check 16 14 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_16_14_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0, 2] }

theorem case_16_14_5_checked :
    (Witness.linear .positive case_16_14_5).check 16 14 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_16_14_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5] }

theorem case_16_14_6_checked :
    (Witness.linear .positive case_16_14_6).check 16 14 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_16_14_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14] }

theorem case_16_14_7_checked :
    (Witness.linear .positive case_16_14_7).check 16 14 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_16_14_8 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_16_14_8_checked :
    (Witness.linear .negative case_16_14_8).check 16 14 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_15_1_checked :
    (Witness.rising).check 16 15 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_15_2_checked :
    (Witness.rising).check 16 15 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_15_3_checked :
    (Witness.rising).check 16 15 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_16_15_4_checked :
    (Witness.rising).check 16 15 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_16_15_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0] }

theorem case_16_15_5_checked :
    (Witness.linear .positive case_16_15_5).check 16 15 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_16_15_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0] }

theorem case_16_15_6_checked :
    (Witness.linear .positive case_16_15_6).check 16 15 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_16_15_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0] }

theorem case_16_15_7_checked :
    (Witness.linear .positive case_16_15_7).check 16 15 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_16_15_8 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_16_15_8_checked :
    (Witness.linear .negative case_16_15_8).check 16 15 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_16_15_9 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_16_15_9_checked :
    (Witness.linear .negative case_16_15_9).check 16 15 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_16 (a k : ℕ) (h : Domain 16 a k) :
    ∃ w : Witness, w.check 16 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 8 ≤ a := by omega
  have haHi : a ≤ 15 := by omega
  interval_cases a

  · have hkHi : k ≤ 4 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_16_8_1_checked⟩

    · exact ⟨Witness.rising, case_16_8_2_checked⟩

    · exact ⟨Witness.rising, case_16_8_3_checked⟩

    · exact ⟨Witness.rising, case_16_8_4_checked⟩

  · have hkHi : k ≤ 5 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_16_9_1_checked⟩

    · exact ⟨Witness.rising, case_16_9_2_checked⟩

    · exact ⟨Witness.rising, case_16_9_3_checked⟩

    · exact ⟨Witness.rising, case_16_9_4_checked⟩

    · exact ⟨Witness.linear .positive case_16_9_5, case_16_9_5_checked⟩

  · have hkHi : k ≤ 6 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_16_10_1_checked⟩

    · exact ⟨Witness.rising, case_16_10_2_checked⟩

    · exact ⟨Witness.rising, case_16_10_3_checked⟩

    · exact ⟨Witness.rising, case_16_10_4_checked⟩

    · exact ⟨Witness.linear .positive case_16_10_5, case_16_10_5_checked⟩

    · exact ⟨Witness.linear .conditional case_16_10_6, case_16_10_6_checked⟩

  · have hkHi : k ≤ 6 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_16_11_1_checked⟩

    · exact ⟨Witness.rising, case_16_11_2_checked⟩

    · exact ⟨Witness.rising, case_16_11_3_checked⟩

    · exact ⟨Witness.rising, case_16_11_4_checked⟩

    · exact ⟨Witness.linear .positive case_16_11_5, case_16_11_5_checked⟩

    · exact ⟨Witness.linear .conditional case_16_11_6, case_16_11_6_checked⟩

  · have hkHi : k ≤ 7 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_16_12_1_checked⟩

    · exact ⟨Witness.rising, case_16_12_2_checked⟩

    · exact ⟨Witness.rising, case_16_12_3_checked⟩

    · exact ⟨Witness.rising, case_16_12_4_checked⟩

    · exact ⟨Witness.linear .positive case_16_12_5, case_16_12_5_checked⟩

    · exact ⟨Witness.linear .positive case_16_12_6, case_16_12_6_checked⟩

    · exact ⟨Witness.linear .negative case_16_12_7, case_16_12_7_checked⟩

  · have hkHi : k ≤ 8 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_16_13_1_checked⟩

    · exact ⟨Witness.rising, case_16_13_2_checked⟩

    · exact ⟨Witness.rising, case_16_13_3_checked⟩

    · exact ⟨Witness.rising, case_16_13_4_checked⟩

    · exact ⟨Witness.linear .positive case_16_13_5, case_16_13_5_checked⟩

    · exact ⟨Witness.linear .positive case_16_13_6, case_16_13_6_checked⟩

    · exact ⟨Witness.linear .negative case_16_13_7, case_16_13_7_checked⟩

    · exact ⟨Witness.linear .negative case_16_13_8, case_16_13_8_checked⟩

  · have hkHi : k ≤ 8 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_16_14_1_checked⟩

    · exact ⟨Witness.rising, case_16_14_2_checked⟩

    · exact ⟨Witness.rising, case_16_14_3_checked⟩

    · exact ⟨Witness.rising, case_16_14_4_checked⟩

    · exact ⟨Witness.linear .positive case_16_14_5, case_16_14_5_checked⟩

    · exact ⟨Witness.linear .positive case_16_14_6, case_16_14_6_checked⟩

    · exact ⟨Witness.linear .positive case_16_14_7, case_16_14_7_checked⟩

    · exact ⟨Witness.linear .negative case_16_14_8, case_16_14_8_checked⟩

  · have hkHi : k ≤ 9 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_16_15_1_checked⟩

    · exact ⟨Witness.rising, case_16_15_2_checked⟩

    · exact ⟨Witness.rising, case_16_15_3_checked⟩

    · exact ⟨Witness.rising, case_16_15_4_checked⟩

    · exact ⟨Witness.linear .positive case_16_15_5, case_16_15_5_checked⟩

    · exact ⟨Witness.linear .positive case_16_15_6, case_16_15_6_checked⟩

    · exact ⟨Witness.linear .positive case_16_15_7, case_16_15_7_checked⟩

    · exact ⟨Witness.linear .negative case_16_15_8, case_16_15_8_checked⟩

    · exact ⟨Witness.linear .negative case_16_15_9, case_16_15_9_checked⟩


#print axioms coverage_16
end ForestUnimodality.FiniteRows.FiniteData
