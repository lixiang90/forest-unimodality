import ForestUnimodality.FiniteWitness
import Mathlib.Tactic.IntervalCases

/-! Generated candidate witnesses. Each sign is rechecked by the Lean kernel.
The coverage theorem quantifies over Domain, independently of this record list.
Source and integer-witness hashes are recorded in research/finite-integer-witnesses/manifest.json.
-/
namespace ForestUnimodality.FiniteRows.FiniteData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_17_9_1_checked :
    (Witness.rising).check 17 9 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_9_2_checked :
    (Witness.rising).check 17 9 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_9_3_checked :
    (Witness.rising).check 17 9 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_9_4_checked :
    (Witness.rising).check 17 9 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_17_9_5 : Certificate := {
  objectiveScale := 129000000
  eta := 2708729100
  rows := #[⟨.count 2, 645051600⟩, ⟨.count 3, 193538700⟩, ⟨.count 4, 129010320⟩, ⟨.path 5, 64500800⟩, ⟨.privateRow 6 0, 10748925⟩, ⟨.hall 4 2, 2148624⟩]
  caps := #[0, 326900, 0, 0, 0, 29180, 0, 0, 0] }

theorem case_17_9_5_checked :
    (Witness.linear .positive case_17_9_5).check 17 9 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_10_1_checked :
    (Witness.rising).check 17 10 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_10_2_checked :
    (Witness.rising).check 17 10 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_10_3_checked :
    (Witness.rising).check 17 10 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_10_4_checked :
    (Witness.rising).check 17 10 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_17_10_5 : Certificate := {
  objectiveScale := 12500
  eta := 262500
  rows := #[⟨.count 2, 62510⟩, ⟨.count 3, 18753⟩, ⟨.count 4, 12495⟩, ⟨.path 5, 6250⟩]
  caps := #[0, 0, 0, 0, 5, 0, 0, 0] }

theorem case_17_10_5_checked :
    (Witness.linear .positive case_17_10_5).check 17 10 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_17_10_6 : Certificate := {
  objectiveScale := 100500000
  eta := 325861200
  rows := #[⟨.count 2, 64862700⟩, ⟨.count 3, 42632100⟩, ⟨.count 6, 301379400⟩, ⟨.count 7, 100459800⟩, ⟨.path 3, 42618240⟩, ⟨.privateRow 2 5, 31481625⟩, ⟨.privateRow 2 6, 76658050⟩, ⟨.privateRow 2 7, 73093650⟩, ⟨.privateRow 3 3, 33205200⟩, ⟨.privateRow 3 4, 40197990⟩, ⟨.privateRow 3 5, 21320740⟩, ⟨.privateRow 4 1, 24903900⟩, ⟨.privateRow 4 2, 19260423⟩, ⟨.privateRow 5 0, 19327490⟩]
  caps := #[0, 0, 41545, 0, 0, 0, 120600, 40200] }

theorem case_17_10_6_checked :
    (Witness.linear .negative case_17_10_6).check 17 10 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_11_1_checked :
    (Witness.rising).check 17 11 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_11_2_checked :
    (Witness.rising).check 17 11 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_11_3_checked :
    (Witness.rising).check 17 11 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_11_4_checked :
    (Witness.rising).check 17 11 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_17_11_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0, 2, 1, 1, 0, 0] }

theorem case_17_11_5_checked :
    (Witness.linear .positive case_17_11_5).check 17 11 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_17_11_6 : Certificate := {
  objectiveScale := 15
  eta := 51
  rows := #[⟨.assumptionRow 6, 14⟩]
  caps := #[0, 0, 27, 14, 14, 65, 46] }

theorem case_17_11_6_checked :
    (Witness.linear .conditional case_17_11_6).check 17 11 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_12_1_checked :
    (Witness.rising).check 17 12 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_12_2_checked :
    (Witness.rising).check 17 12 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_12_3_checked :
    (Witness.rising).check 17 12 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_12_4_checked :
    (Witness.rising).check 17 12 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_17_12_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0, 2, 1, 1, 0] }

theorem case_17_12_5_checked :
    (Witness.linear .positive case_17_12_5).check 17 12 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_17_12_6 : Certificate := {
  objectiveScale := 5
  eta := 56
  rows := #[⟨.assumptionRow 6, 9⟩]
  caps := #[0, 0, 25, 13, 9, 16] }

theorem case_17_12_6_checked :
    (Witness.linear .conditional case_17_12_6).check 17 12 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_17_12_7 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 14, 14] }

theorem case_17_12_7_checked :
    (Witness.linear .negative case_17_12_7).check 17 12 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_13_1_checked :
    (Witness.rising).check 17 13 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_13_2_checked :
    (Witness.rising).check 17 13 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_13_3_checked :
    (Witness.rising).check 17 13 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_13_4_checked :
    (Witness.rising).check 17 13 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_17_13_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0, 2, 1, 1] }

theorem case_17_13_5_checked :
    (Witness.linear .positive case_17_13_5).check 17 13 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_17_13_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1] }

theorem case_17_13_6_checked :
    (Witness.linear .positive case_17_13_6).check 17 13 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_17_13_7 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 42, 42] }

theorem case_17_13_7_checked :
    (Witness.linear .negative case_17_13_7).check 17 13 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_17_13_8 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_17_13_8_checked :
    (Witness.linear .negative case_17_13_8).check 17 13 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_14_1_checked :
    (Witness.rising).check 17 14 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_14_2_checked :
    (Witness.rising).check 17 14 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_14_3_checked :
    (Witness.rising).check 17 14 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_14_4_checked :
    (Witness.rising).check 17 14 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_17_14_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0, 2, 1] }

theorem case_17_14_5_checked :
    (Witness.linear .positive case_17_14_5).check 17 14 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_17_14_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2] }

theorem case_17_14_6_checked :
    (Witness.linear .positive case_17_14_6).check 17 14 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_17_14_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5] }

theorem case_17_14_7_checked :
    (Witness.linear .positive case_17_14_7).check 17 14 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_17_14_8 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_17_14_8_checked :
    (Witness.linear .negative case_17_14_8).check 17 14 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_15_1_checked :
    (Witness.rising).check 17 15 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_15_2_checked :
    (Witness.rising).check 17 15 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_15_3_checked :
    (Witness.rising).check 17 15 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_15_4_checked :
    (Witness.rising).check 17 15 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_17_15_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0, 2] }

theorem case_17_15_5_checked :
    (Witness.linear .positive case_17_15_5).check 17 15 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_17_15_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5] }

theorem case_17_15_6_checked :
    (Witness.linear .positive case_17_15_6).check 17 15 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_17_15_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14] }

theorem case_17_15_7_checked :
    (Witness.linear .positive case_17_15_7).check 17 15 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_17_15_8 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_17_15_8_checked :
    (Witness.linear .negative case_17_15_8).check 17 15 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_17_15_9 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_17_15_9_checked :
    (Witness.linear .negative case_17_15_9).check 17 15 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_16_1_checked :
    (Witness.rising).check 17 16 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_16_2_checked :
    (Witness.rising).check 17 16 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_16_3_checked :
    (Witness.rising).check 17 16 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_17_16_4_checked :
    (Witness.rising).check 17 16 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_17_16_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0] }

theorem case_17_16_5_checked :
    (Witness.linear .positive case_17_16_5).check 17 16 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_17_16_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0] }

theorem case_17_16_6_checked :
    (Witness.linear .positive case_17_16_6).check 17 16 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_17_16_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0] }

theorem case_17_16_7_checked :
    (Witness.linear .positive case_17_16_7).check 17 16 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_17_16_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0] }

theorem case_17_16_8_checked :
    (Witness.linear .positive case_17_16_8).check 17 16 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_17_16_9 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_17_16_9_checked :
    (Witness.linear .negative case_17_16_9).check 17 16 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_17_16_10 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_17_16_10_checked :
    (Witness.linear .negative case_17_16_10).check 17 16 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_17 (a k : ℕ) (h : Domain 17 a k) :
    ∃ w : Witness, w.check 17 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 9 ≤ a := by omega
  have haHi : a ≤ 16 := by omega
  interval_cases a

  · have hkHi : k ≤ 5 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_17_9_1_checked⟩

    · exact ⟨Witness.rising, case_17_9_2_checked⟩

    · exact ⟨Witness.rising, case_17_9_3_checked⟩

    · exact ⟨Witness.rising, case_17_9_4_checked⟩

    · exact ⟨Witness.linear .positive case_17_9_5, case_17_9_5_checked⟩

  · have hkHi : k ≤ 6 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_17_10_1_checked⟩

    · exact ⟨Witness.rising, case_17_10_2_checked⟩

    · exact ⟨Witness.rising, case_17_10_3_checked⟩

    · exact ⟨Witness.rising, case_17_10_4_checked⟩

    · exact ⟨Witness.linear .positive case_17_10_5, case_17_10_5_checked⟩

    · exact ⟨Witness.linear .negative case_17_10_6, case_17_10_6_checked⟩

  · have hkHi : k ≤ 6 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_17_11_1_checked⟩

    · exact ⟨Witness.rising, case_17_11_2_checked⟩

    · exact ⟨Witness.rising, case_17_11_3_checked⟩

    · exact ⟨Witness.rising, case_17_11_4_checked⟩

    · exact ⟨Witness.linear .positive case_17_11_5, case_17_11_5_checked⟩

    · exact ⟨Witness.linear .conditional case_17_11_6, case_17_11_6_checked⟩

  · have hkHi : k ≤ 7 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_17_12_1_checked⟩

    · exact ⟨Witness.rising, case_17_12_2_checked⟩

    · exact ⟨Witness.rising, case_17_12_3_checked⟩

    · exact ⟨Witness.rising, case_17_12_4_checked⟩

    · exact ⟨Witness.linear .positive case_17_12_5, case_17_12_5_checked⟩

    · exact ⟨Witness.linear .conditional case_17_12_6, case_17_12_6_checked⟩

    · exact ⟨Witness.linear .negative case_17_12_7, case_17_12_7_checked⟩

  · have hkHi : k ≤ 8 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_17_13_1_checked⟩

    · exact ⟨Witness.rising, case_17_13_2_checked⟩

    · exact ⟨Witness.rising, case_17_13_3_checked⟩

    · exact ⟨Witness.rising, case_17_13_4_checked⟩

    · exact ⟨Witness.linear .positive case_17_13_5, case_17_13_5_checked⟩

    · exact ⟨Witness.linear .positive case_17_13_6, case_17_13_6_checked⟩

    · exact ⟨Witness.linear .negative case_17_13_7, case_17_13_7_checked⟩

    · exact ⟨Witness.linear .negative case_17_13_8, case_17_13_8_checked⟩

  · have hkHi : k ≤ 8 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_17_14_1_checked⟩

    · exact ⟨Witness.rising, case_17_14_2_checked⟩

    · exact ⟨Witness.rising, case_17_14_3_checked⟩

    · exact ⟨Witness.rising, case_17_14_4_checked⟩

    · exact ⟨Witness.linear .positive case_17_14_5, case_17_14_5_checked⟩

    · exact ⟨Witness.linear .positive case_17_14_6, case_17_14_6_checked⟩

    · exact ⟨Witness.linear .positive case_17_14_7, case_17_14_7_checked⟩

    · exact ⟨Witness.linear .negative case_17_14_8, case_17_14_8_checked⟩

  · have hkHi : k ≤ 9 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_17_15_1_checked⟩

    · exact ⟨Witness.rising, case_17_15_2_checked⟩

    · exact ⟨Witness.rising, case_17_15_3_checked⟩

    · exact ⟨Witness.rising, case_17_15_4_checked⟩

    · exact ⟨Witness.linear .positive case_17_15_5, case_17_15_5_checked⟩

    · exact ⟨Witness.linear .positive case_17_15_6, case_17_15_6_checked⟩

    · exact ⟨Witness.linear .positive case_17_15_7, case_17_15_7_checked⟩

    · exact ⟨Witness.linear .negative case_17_15_8, case_17_15_8_checked⟩

    · exact ⟨Witness.linear .negative case_17_15_9, case_17_15_9_checked⟩

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_17_16_1_checked⟩

    · exact ⟨Witness.rising, case_17_16_2_checked⟩

    · exact ⟨Witness.rising, case_17_16_3_checked⟩

    · exact ⟨Witness.rising, case_17_16_4_checked⟩

    · exact ⟨Witness.linear .positive case_17_16_5, case_17_16_5_checked⟩

    · exact ⟨Witness.linear .positive case_17_16_6, case_17_16_6_checked⟩

    · exact ⟨Witness.linear .positive case_17_16_7, case_17_16_7_checked⟩

    · exact ⟨Witness.linear .positive case_17_16_8, case_17_16_8_checked⟩

    · exact ⟨Witness.linear .negative case_17_16_9, case_17_16_9_checked⟩

    · exact ⟨Witness.linear .negative case_17_16_10, case_17_16_10_checked⟩


#print axioms coverage_17
end ForestUnimodality.FiniteRows.FiniteData
