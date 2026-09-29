import ForestUnimodality.FiniteWitness
import Mathlib.Tactic.IntervalCases

/-! Generated candidate witnesses. Each sign is rechecked by the Lean kernel.
The coverage theorem quantifies over Domain, independently of this record list.
Source and integer-witness hashes are recorded in research/finite-integer-witnesses/manifest.json.
-/
namespace ForestUnimodality.FiniteRows.FiniteData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_13_7_1_checked :
    (Witness.rising).check 13 7 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_13_7_2_checked :
    (Witness.rising).check 13 7 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_13_7_3_checked :
    (Witness.rising).check 13 7 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_13_7_4 : Certificate := {
  objectiveScale := 280000
  eta := 2333450
  rows := #[⟨.count 2, 560000⟩, ⟨.count 3, 280035⟩, ⟨.path 4, 186672⟩]
  caps := #[0, 0, 32, 0, 0, 0, 0] }

theorem case_13_7_4_checked :
    (Witness.linear .positive case_13_7_4).check 13 7 4 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_13_8_1_checked :
    (Witness.rising).check 13 8 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_13_8_2_checked :
    (Witness.rising).check 13 8 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_13_8_3_checked :
    (Witness.rising).check 13 8 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_13_8_4 : Certificate := {
  objectiveScale := 350000
  eta := 2450070
  rows := #[⟨.count 2, 630000⟩, ⟨.count 3, 349965⟩, ⟨.path 4, 210006⟩]
  caps := #[0, 140, 18, 35, 0, 0] }

theorem case_13_8_4_checked :
    (Witness.linear .positive case_13_8_4).check 13 8 4 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_13_9_1_checked :
    (Witness.rising).check 13 9 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_13_9_2_checked :
    (Witness.rising).check 13 9 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_13_9_3_checked :
    (Witness.rising).check 13 9 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_13_9_4 : Certificate := {
  objectiveScale := 1
  eta := 2
  rows := #[]
  caps := #[0, 0, 1, 1, 0] }

theorem case_13_9_4_checked :
    (Witness.linear .positive case_13_9_4).check 13 9 4 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_13_9_5 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 5, 5] }

theorem case_13_9_5_checked :
    (Witness.linear .negative case_13_9_5).check 13 9 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_13_10_1_checked :
    (Witness.rising).check 13 10 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_13_10_2_checked :
    (Witness.rising).check 13 10 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_13_10_3_checked :
    (Witness.rising).check 13 10 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_13_10_4 : Certificate := {
  objectiveScale := 1
  eta := 2
  rows := #[]
  caps := #[0, 0, 1, 1] }

theorem case_13_10_4_checked :
    (Witness.linear .positive case_13_10_4).check 13 10 4 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_13_10_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0, 2, 1] }

theorem case_13_10_5_checked :
    (Witness.linear .positive case_13_10_5).check 13 10 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_13_10_6 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_13_10_6_checked :
    (Witness.linear .negative case_13_10_6).check 13 10 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_13_11_1_checked :
    (Witness.rising).check 13 11 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_13_11_2_checked :
    (Witness.rising).check 13 11 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_13_11_3_checked :
    (Witness.rising).check 13 11 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_13_11_4 : Certificate := {
  objectiveScale := 1
  eta := 2
  rows := #[]
  caps := #[0, 0, 1] }

theorem case_13_11_4_checked :
    (Witness.linear .positive case_13_11_4).check 13 11 4 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_13_11_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0, 2] }

theorem case_13_11_5_checked :
    (Witness.linear .positive case_13_11_5).check 13 11 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_13_11_6 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_13_11_6_checked :
    (Witness.linear .negative case_13_11_6).check 13 11 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_13_12_1_checked :
    (Witness.rising).check 13 12 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_13_12_2_checked :
    (Witness.rising).check 13 12 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_13_12_3_checked :
    (Witness.rising).check 13 12 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_13_12_4 : Certificate := {
  objectiveScale := 1
  eta := 2
  rows := #[]
  caps := #[0, 0] }

theorem case_13_12_4_checked :
    (Witness.linear .positive case_13_12_4).check 13 12 4 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_13_12_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0] }

theorem case_13_12_5_checked :
    (Witness.linear .positive case_13_12_5).check 13 12 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_13_12_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0] }

theorem case_13_12_6_checked :
    (Witness.linear .positive case_13_12_6).check 13 12 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_13_12_7 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_13_12_7_checked :
    (Witness.linear .negative case_13_12_7).check 13 12 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_13 (a k : ℕ) (h : Domain 13 a k) :
    ∃ w : Witness, w.check 13 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 7 ≤ a := by omega
  have haHi : a ≤ 12 := by omega
  interval_cases a

  · have hkHi : k ≤ 4 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_13_7_1_checked⟩

    · exact ⟨Witness.rising, case_13_7_2_checked⟩

    · exact ⟨Witness.rising, case_13_7_3_checked⟩

    · exact ⟨Witness.linear .positive case_13_7_4, case_13_7_4_checked⟩

  · have hkHi : k ≤ 4 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_13_8_1_checked⟩

    · exact ⟨Witness.rising, case_13_8_2_checked⟩

    · exact ⟨Witness.rising, case_13_8_3_checked⟩

    · exact ⟨Witness.linear .positive case_13_8_4, case_13_8_4_checked⟩

  · have hkHi : k ≤ 5 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_13_9_1_checked⟩

    · exact ⟨Witness.rising, case_13_9_2_checked⟩

    · exact ⟨Witness.rising, case_13_9_3_checked⟩

    · exact ⟨Witness.linear .positive case_13_9_4, case_13_9_4_checked⟩

    · exact ⟨Witness.linear .negative case_13_9_5, case_13_9_5_checked⟩

  · have hkHi : k ≤ 6 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_13_10_1_checked⟩

    · exact ⟨Witness.rising, case_13_10_2_checked⟩

    · exact ⟨Witness.rising, case_13_10_3_checked⟩

    · exact ⟨Witness.linear .positive case_13_10_4, case_13_10_4_checked⟩

    · exact ⟨Witness.linear .positive case_13_10_5, case_13_10_5_checked⟩

    · exact ⟨Witness.linear .negative case_13_10_6, case_13_10_6_checked⟩

  · have hkHi : k ≤ 6 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_13_11_1_checked⟩

    · exact ⟨Witness.rising, case_13_11_2_checked⟩

    · exact ⟨Witness.rising, case_13_11_3_checked⟩

    · exact ⟨Witness.linear .positive case_13_11_4, case_13_11_4_checked⟩

    · exact ⟨Witness.linear .positive case_13_11_5, case_13_11_5_checked⟩

    · exact ⟨Witness.linear .negative case_13_11_6, case_13_11_6_checked⟩

  · have hkHi : k ≤ 7 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_13_12_1_checked⟩

    · exact ⟨Witness.rising, case_13_12_2_checked⟩

    · exact ⟨Witness.rising, case_13_12_3_checked⟩

    · exact ⟨Witness.linear .positive case_13_12_4, case_13_12_4_checked⟩

    · exact ⟨Witness.linear .positive case_13_12_5, case_13_12_5_checked⟩

    · exact ⟨Witness.linear .positive case_13_12_6, case_13_12_6_checked⟩

    · exact ⟨Witness.linear .negative case_13_12_7, case_13_12_7_checked⟩


#print axioms coverage_13
end ForestUnimodality.FiniteRows.FiniteData
