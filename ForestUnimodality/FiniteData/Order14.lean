import ForestUnimodality.FiniteWitness
import Mathlib.Tactic.IntervalCases

/-! Generated candidate witnesses. Each sign is rechecked by the Lean kernel.
The coverage theorem quantifies over Domain, independently of this record list.
Source and integer-witness hashes are recorded in research/finite-integer-witnesses/manifest.json.
-/
namespace ForestUnimodality.FiniteRows.FiniteData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_14_7_1_checked :
    (Witness.rising).check 14 7 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_14_7_2_checked :
    (Witness.rising).check 14 7 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_14_7_3_checked :
    (Witness.rising).check 14 7 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_14_7_4_checked :
    (Witness.rising).check 14 7 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_14_8_1_checked :
    (Witness.rising).check 14 8 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_14_8_2_checked :
    (Witness.rising).check 14 8 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_14_8_3_checked :
    (Witness.rising).check 14 8 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_14_8_4_checked :
    (Witness.rising).check 14 8 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_14_9_1_checked :
    (Witness.rising).check 14 9 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_14_9_2_checked :
    (Witness.rising).check 14 9 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_14_9_3_checked :
    (Witness.rising).check 14 9 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_14_9_4_checked :
    (Witness.rising).check 14 9 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_14_9_5 : Certificate := {
  objectiveScale := 2
  eta := 1
  rows := #[⟨.assumptionRow 5, 1⟩]
  caps := #[0, 0, 1, 1, 6, 5] }

theorem case_14_9_5_checked :
    (Witness.linear .conditional case_14_9_5).check 14 9 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_14_10_1_checked :
    (Witness.rising).check 14 10 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_14_10_2_checked :
    (Witness.rising).check 14 10 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_14_10_3_checked :
    (Witness.rising).check 14 10 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_14_10_4_checked :
    (Witness.rising).check 14 10 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_14_10_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0, 2, 1, 1] }

theorem case_14_10_5_checked :
    (Witness.linear .positive case_14_10_5).check 14 10 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_14_10_6 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 5] }

theorem case_14_10_6_checked :
    (Witness.linear .negative case_14_10_6).check 14 10 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_14_11_1_checked :
    (Witness.rising).check 14 11 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_14_11_2_checked :
    (Witness.rising).check 14 11 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_14_11_3_checked :
    (Witness.rising).check 14 11 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_14_11_4_checked :
    (Witness.rising).check 14 11 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_14_11_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0, 2, 1] }

theorem case_14_11_5_checked :
    (Witness.linear .positive case_14_11_5).check 14 11 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_14_11_6 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 14] }

theorem case_14_11_6_checked :
    (Witness.linear .negative case_14_11_6).check 14 11 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_14_12_1_checked :
    (Witness.rising).check 14 12 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_14_12_2_checked :
    (Witness.rising).check 14 12 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_14_12_3_checked :
    (Witness.rising).check 14 12 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_14_12_4 : Certificate := {
  objectiveScale := 1
  eta := 2
  rows := #[]
  caps := #[0, 0, 1] }

theorem case_14_12_4_checked :
    (Witness.linear .positive case_14_12_4).check 14 12 4 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_14_12_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0, 2] }

theorem case_14_12_5_checked :
    (Witness.linear .positive case_14_12_5).check 14 12 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_14_12_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5] }

theorem case_14_12_6_checked :
    (Witness.linear .positive case_14_12_6).check 14 12 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_14_12_7 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_14_12_7_checked :
    (Witness.linear .negative case_14_12_7).check 14 12 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_14_13_1_checked :
    (Witness.rising).check 14 13 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_14_13_2_checked :
    (Witness.rising).check 14 13 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_14_13_3_checked :
    (Witness.rising).check 14 13 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_14_13_4 : Certificate := {
  objectiveScale := 1
  eta := 2
  rows := #[]
  caps := #[0, 0] }

theorem case_14_13_4_checked :
    (Witness.linear .positive case_14_13_4).check 14 13 4 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_14_13_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0] }

theorem case_14_13_5_checked :
    (Witness.linear .positive case_14_13_5).check 14 13 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_14_13_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0] }

theorem case_14_13_6_checked :
    (Witness.linear .positive case_14_13_6).check 14 13 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_14_13_7 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_14_13_7_checked :
    (Witness.linear .negative case_14_13_7).check 14 13 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_14_13_8 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_14_13_8_checked :
    (Witness.linear .negative case_14_13_8).check 14 13 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_14 (a k : ℕ) (h : Domain 14 a k) :
    ∃ w : Witness, w.check 14 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 7 ≤ a := by omega
  have haHi : a ≤ 13 := by omega
  interval_cases a

  · have hkHi : k ≤ 4 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_14_7_1_checked⟩

    · exact ⟨Witness.rising, case_14_7_2_checked⟩

    · exact ⟨Witness.rising, case_14_7_3_checked⟩

    · exact ⟨Witness.rising, case_14_7_4_checked⟩

  · have hkHi : k ≤ 4 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_14_8_1_checked⟩

    · exact ⟨Witness.rising, case_14_8_2_checked⟩

    · exact ⟨Witness.rising, case_14_8_3_checked⟩

    · exact ⟨Witness.rising, case_14_8_4_checked⟩

  · have hkHi : k ≤ 5 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_14_9_1_checked⟩

    · exact ⟨Witness.rising, case_14_9_2_checked⟩

    · exact ⟨Witness.rising, case_14_9_3_checked⟩

    · exact ⟨Witness.rising, case_14_9_4_checked⟩

    · exact ⟨Witness.linear .conditional case_14_9_5, case_14_9_5_checked⟩

  · have hkHi : k ≤ 6 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_14_10_1_checked⟩

    · exact ⟨Witness.rising, case_14_10_2_checked⟩

    · exact ⟨Witness.rising, case_14_10_3_checked⟩

    · exact ⟨Witness.rising, case_14_10_4_checked⟩

    · exact ⟨Witness.linear .positive case_14_10_5, case_14_10_5_checked⟩

    · exact ⟨Witness.linear .negative case_14_10_6, case_14_10_6_checked⟩

  · have hkHi : k ≤ 6 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_14_11_1_checked⟩

    · exact ⟨Witness.rising, case_14_11_2_checked⟩

    · exact ⟨Witness.rising, case_14_11_3_checked⟩

    · exact ⟨Witness.rising, case_14_11_4_checked⟩

    · exact ⟨Witness.linear .positive case_14_11_5, case_14_11_5_checked⟩

    · exact ⟨Witness.linear .negative case_14_11_6, case_14_11_6_checked⟩

  · have hkHi : k ≤ 7 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_14_12_1_checked⟩

    · exact ⟨Witness.rising, case_14_12_2_checked⟩

    · exact ⟨Witness.rising, case_14_12_3_checked⟩

    · exact ⟨Witness.linear .positive case_14_12_4, case_14_12_4_checked⟩

    · exact ⟨Witness.linear .positive case_14_12_5, case_14_12_5_checked⟩

    · exact ⟨Witness.linear .positive case_14_12_6, case_14_12_6_checked⟩

    · exact ⟨Witness.linear .negative case_14_12_7, case_14_12_7_checked⟩

  · have hkHi : k ≤ 8 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_14_13_1_checked⟩

    · exact ⟨Witness.rising, case_14_13_2_checked⟩

    · exact ⟨Witness.rising, case_14_13_3_checked⟩

    · exact ⟨Witness.linear .positive case_14_13_4, case_14_13_4_checked⟩

    · exact ⟨Witness.linear .positive case_14_13_5, case_14_13_5_checked⟩

    · exact ⟨Witness.linear .positive case_14_13_6, case_14_13_6_checked⟩

    · exact ⟨Witness.linear .negative case_14_13_7, case_14_13_7_checked⟩

    · exact ⟨Witness.linear .negative case_14_13_8, case_14_13_8_checked⟩


#print axioms coverage_14
end ForestUnimodality.FiniteRows.FiniteData
