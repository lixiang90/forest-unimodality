import ForestUnimodality.FiniteWitness
import Mathlib.Tactic.IntervalCases

/-! Generated candidate witnesses. Each sign is rechecked by the Lean kernel.
The coverage theorem quantifies over Domain, independently of this record list.
Source and integer-witness hashes are recorded in research/finite-integer-witnesses/manifest.json.
-/
namespace ForestUnimodality.FiniteRows.FiniteData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_15_8_1_checked :
    (Witness.rising).check 15 8 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_15_8_2_checked :
    (Witness.rising).check 15 8 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_15_8_3_checked :
    (Witness.rising).check 15 8 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_15_8_4_checked :
    (Witness.rising).check 15 8 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_15_9_1_checked :
    (Witness.rising).check 15 9 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_15_9_2_checked :
    (Witness.rising).check 15 9 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_15_9_3_checked :
    (Witness.rising).check 15 9 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_15_9_4_checked :
    (Witness.rising).check 15 9 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_15_9_5 : Certificate := {
  objectiveScale := 103320000
  eta := 803485200
  rows := #[⟨.count 2, 272902560⟩, ⟨.count 3, 156426480⟩, ⟨.count 4, 124328400⟩, ⟨.path 4, 63422800⟩, ⟨.privateRow 3 3, 4094055⟩, ⟨.privateRow 3 4, 14769020⟩, ⟨.privateRow 4 1, 16028376⟩, ⟨.privateRow 6 0, 25830000⟩, ⟨.hall 4 1, 16014600⟩, ⟨.assumptionRow 5, 92978160⟩]
  caps := #[0, 17360, 15120, 8830, 15808, 9840, 0] }

theorem case_15_9_5_checked :
    (Witness.linear .conditional case_15_9_5).check 15 9 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_15_10_1_checked :
    (Witness.rising).check 15 10 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_15_10_2_checked :
    (Witness.rising).check 15 10 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_15_10_3_checked :
    (Witness.rising).check 15 10 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_15_10_4_checked :
    (Witness.rising).check 15 10 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_15_10_5 : Certificate := {
  objectiveScale := 2
  eta := 7
  rows := #[⟨.assumptionRow 5, 3⟩]
  caps := #[0, 0, 4, 3, 3, 5] }

theorem case_15_10_5_checked :
    (Witness.linear .conditional case_15_10_5).check 15 10 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_15_10_6 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 5, 5] }

theorem case_15_10_6_checked :
    (Witness.linear .negative case_15_10_6).check 15 10 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_15_11_1_checked :
    (Witness.rising).check 15 11 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_15_11_2_checked :
    (Witness.rising).check 15 11 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_15_11_3_checked :
    (Witness.rising).check 15 11 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_15_11_4_checked :
    (Witness.rising).check 15 11 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_15_11_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0, 2, 1, 1] }

theorem case_15_11_5_checked :
    (Witness.linear .positive case_15_11_5).check 15 11 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_15_11_6 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 14, 14] }

theorem case_15_11_6_checked :
    (Witness.linear .negative case_15_11_6).check 15 11 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_15_12_1_checked :
    (Witness.rising).check 15 12 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_15_12_2_checked :
    (Witness.rising).check 15 12 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_15_12_3_checked :
    (Witness.rising).check 15 12 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_15_12_4_checked :
    (Witness.rising).check 15 12 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_15_12_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0, 2, 1] }

theorem case_15_12_5_checked :
    (Witness.linear .positive case_15_12_5).check 15 12 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_15_12_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2] }

theorem case_15_12_6_checked :
    (Witness.linear .positive case_15_12_6).check 15 12 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_15_12_7 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_15_12_7_checked :
    (Witness.linear .negative case_15_12_7).check 15 12 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_15_13_1_checked :
    (Witness.rising).check 15 13 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_15_13_2_checked :
    (Witness.rising).check 15 13 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_15_13_3_checked :
    (Witness.rising).check 15 13 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_15_13_4_checked :
    (Witness.rising).check 15 13 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_15_13_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0, 2] }

theorem case_15_13_5_checked :
    (Witness.linear .positive case_15_13_5).check 15 13 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_15_13_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5] }

theorem case_15_13_6_checked :
    (Witness.linear .positive case_15_13_6).check 15 13 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_15_13_7 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_15_13_7_checked :
    (Witness.linear .negative case_15_13_7).check 15 13 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_15_13_8 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_15_13_8_checked :
    (Witness.linear .negative case_15_13_8).check 15 13 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_15_14_1_checked :
    (Witness.rising).check 15 14 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_15_14_2_checked :
    (Witness.rising).check 15 14 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_15_14_3_checked :
    (Witness.rising).check 15 14 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_15_14_4_checked :
    (Witness.rising).check 15 14 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_15_14_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0] }

theorem case_15_14_5_checked :
    (Witness.linear .positive case_15_14_5).check 15 14 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_15_14_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0] }

theorem case_15_14_6_checked :
    (Witness.linear .positive case_15_14_6).check 15 14 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_15_14_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0] }

theorem case_15_14_7_checked :
    (Witness.linear .positive case_15_14_7).check 15 14 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_15_14_8 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_15_14_8_checked :
    (Witness.linear .negative case_15_14_8).check 15 14 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_15 (a k : ℕ) (h : Domain 15 a k) :
    ∃ w : Witness, w.check 15 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 8 ≤ a := by omega
  have haHi : a ≤ 14 := by omega
  interval_cases a

  · have hkHi : k ≤ 4 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_15_8_1_checked⟩

    · exact ⟨Witness.rising, case_15_8_2_checked⟩

    · exact ⟨Witness.rising, case_15_8_3_checked⟩

    · exact ⟨Witness.rising, case_15_8_4_checked⟩

  · have hkHi : k ≤ 5 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_15_9_1_checked⟩

    · exact ⟨Witness.rising, case_15_9_2_checked⟩

    · exact ⟨Witness.rising, case_15_9_3_checked⟩

    · exact ⟨Witness.rising, case_15_9_4_checked⟩

    · exact ⟨Witness.linear .conditional case_15_9_5, case_15_9_5_checked⟩

  · have hkHi : k ≤ 6 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_15_10_1_checked⟩

    · exact ⟨Witness.rising, case_15_10_2_checked⟩

    · exact ⟨Witness.rising, case_15_10_3_checked⟩

    · exact ⟨Witness.rising, case_15_10_4_checked⟩

    · exact ⟨Witness.linear .conditional case_15_10_5, case_15_10_5_checked⟩

    · exact ⟨Witness.linear .negative case_15_10_6, case_15_10_6_checked⟩

  · have hkHi : k ≤ 6 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_15_11_1_checked⟩

    · exact ⟨Witness.rising, case_15_11_2_checked⟩

    · exact ⟨Witness.rising, case_15_11_3_checked⟩

    · exact ⟨Witness.rising, case_15_11_4_checked⟩

    · exact ⟨Witness.linear .positive case_15_11_5, case_15_11_5_checked⟩

    · exact ⟨Witness.linear .negative case_15_11_6, case_15_11_6_checked⟩

  · have hkHi : k ≤ 7 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_15_12_1_checked⟩

    · exact ⟨Witness.rising, case_15_12_2_checked⟩

    · exact ⟨Witness.rising, case_15_12_3_checked⟩

    · exact ⟨Witness.rising, case_15_12_4_checked⟩

    · exact ⟨Witness.linear .positive case_15_12_5, case_15_12_5_checked⟩

    · exact ⟨Witness.linear .positive case_15_12_6, case_15_12_6_checked⟩

    · exact ⟨Witness.linear .negative case_15_12_7, case_15_12_7_checked⟩

  · have hkHi : k ≤ 8 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_15_13_1_checked⟩

    · exact ⟨Witness.rising, case_15_13_2_checked⟩

    · exact ⟨Witness.rising, case_15_13_3_checked⟩

    · exact ⟨Witness.rising, case_15_13_4_checked⟩

    · exact ⟨Witness.linear .positive case_15_13_5, case_15_13_5_checked⟩

    · exact ⟨Witness.linear .positive case_15_13_6, case_15_13_6_checked⟩

    · exact ⟨Witness.linear .negative case_15_13_7, case_15_13_7_checked⟩

    · exact ⟨Witness.linear .negative case_15_13_8, case_15_13_8_checked⟩

  · have hkHi : k ≤ 8 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_15_14_1_checked⟩

    · exact ⟨Witness.rising, case_15_14_2_checked⟩

    · exact ⟨Witness.rising, case_15_14_3_checked⟩

    · exact ⟨Witness.rising, case_15_14_4_checked⟩

    · exact ⟨Witness.linear .positive case_15_14_5, case_15_14_5_checked⟩

    · exact ⟨Witness.linear .positive case_15_14_6, case_15_14_6_checked⟩

    · exact ⟨Witness.linear .positive case_15_14_7, case_15_14_7_checked⟩

    · exact ⟨Witness.linear .negative case_15_14_8, case_15_14_8_checked⟩


#print axioms coverage_15
end ForestUnimodality.FiniteRows.FiniteData
