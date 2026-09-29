import ForestUnimodality.FiniteWitness
import Mathlib.Tactic.IntervalCases

/-! Generated candidate witnesses. Each sign is rechecked by the Lean kernel.
The coverage theorem quantifies over Domain, independently of this record list.
Source and integer-witness hashes are recorded in research/finite-integer-witnesses/manifest.json.
-/
namespace ForestUnimodality.FiniteRows.FiniteData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_12_6_1_checked :
    (Witness.rising).check 12 6 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_12_6_2_checked :
    (Witness.rising).check 12 6 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_12_6_3_checked :
    (Witness.rising).check 12 6 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_12_7_1_checked :
    (Witness.rising).check 12 7 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_12_7_2_checked :
    (Witness.rising).check 12 7 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_12_7_3_checked :
    (Witness.rising).check 12 7 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_12_7_4 : Certificate := {
  objectiveScale := 1632000
  eta := 1087728
  rows := #[⟨.count 3, 1496136⟩, ⟨.count 4, 3264000⟩, ⟨.count 5, 1632000⟩, ⟨.path 2, 543960⟩, ⟨.privateRow 2 2, 271983⟩, ⟨.privateRow 2 3, 136000⟩, ⟨.privateRow 3 0, 136000⟩]
  caps := #[0, 192, 79, 0, 0, 0] }

theorem case_12_7_4_checked :
    (Witness.linear .negative case_12_7_4).check 12 7 4 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_12_8_1_checked :
    (Witness.rising).check 12 8 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_12_8_2_checked :
    (Witness.rising).check 12 8 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_12_8_3_checked :
    (Witness.rising).check 12 8 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_12_8_4 : Certificate := {
  objectiveScale := 1
  eta := 1
  rows := #[⟨.assumptionRow 4, 1⟩]
  caps := #[0, 0, 1, 1, 2] }

theorem case_12_8_4_checked :
    (Witness.linear .conditional case_12_8_4).check 12 8 4 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_12_9_1_checked :
    (Witness.rising).check 12 9 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_12_9_2_checked :
    (Witness.rising).check 12 9 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_12_9_3_checked :
    (Witness.rising).check 12 9 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_12_9_4 : Certificate := {
  objectiveScale := 1
  eta := 2
  rows := #[]
  caps := #[0, 0, 1, 1] }

theorem case_12_9_4_checked :
    (Witness.linear .positive case_12_9_4).check 12 9 4 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_12_9_5 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 5] }

theorem case_12_9_5_checked :
    (Witness.linear .negative case_12_9_5).check 12 9 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_12_10_1_checked :
    (Witness.rising).check 12 10 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_12_10_2_checked :
    (Witness.rising).check 12 10 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_12_10_3_checked :
    (Witness.rising).check 12 10 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_12_10_4 : Certificate := {
  objectiveScale := 1
  eta := 2
  rows := #[]
  caps := #[0, 0, 1] }

theorem case_12_10_4_checked :
    (Witness.linear .positive case_12_10_4).check 12 10 4 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_12_10_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0, 2] }

theorem case_12_10_5_checked :
    (Witness.linear .positive case_12_10_5).check 12 10 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_12_10_6 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_12_10_6_checked :
    (Witness.linear .negative case_12_10_6).check 12 10 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_12_11_1_checked :
    (Witness.rising).check 12 11 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_12_11_2_checked :
    (Witness.rising).check 12 11 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_12_11_3_checked :
    (Witness.rising).check 12 11 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_12_11_4 : Certificate := {
  objectiveScale := 1
  eta := 2
  rows := #[]
  caps := #[0, 0] }

theorem case_12_11_4_checked :
    (Witness.linear .positive case_12_11_4).check 12 11 4 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_12_11_5 : Certificate := {
  objectiveScale := 1
  eta := 5
  rows := #[]
  caps := #[0, 0] }

theorem case_12_11_5_checked :
    (Witness.linear .positive case_12_11_5).check 12 11 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_12_11_6 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_12_11_6_checked :
    (Witness.linear .negative case_12_11_6).check 12 11 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_12 (a k : ℕ) (h : Domain 12 a k) :
    ∃ w : Witness, w.check 12 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 6 ≤ a := by omega
  have haHi : a ≤ 11 := by omega
  interval_cases a

  · have hkHi : k ≤ 3 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_12_6_1_checked⟩

    · exact ⟨Witness.rising, case_12_6_2_checked⟩

    · exact ⟨Witness.rising, case_12_6_3_checked⟩

  · have hkHi : k ≤ 4 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_12_7_1_checked⟩

    · exact ⟨Witness.rising, case_12_7_2_checked⟩

    · exact ⟨Witness.rising, case_12_7_3_checked⟩

    · exact ⟨Witness.linear .negative case_12_7_4, case_12_7_4_checked⟩

  · have hkHi : k ≤ 4 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_12_8_1_checked⟩

    · exact ⟨Witness.rising, case_12_8_2_checked⟩

    · exact ⟨Witness.rising, case_12_8_3_checked⟩

    · exact ⟨Witness.linear .conditional case_12_8_4, case_12_8_4_checked⟩

  · have hkHi : k ≤ 5 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_12_9_1_checked⟩

    · exact ⟨Witness.rising, case_12_9_2_checked⟩

    · exact ⟨Witness.rising, case_12_9_3_checked⟩

    · exact ⟨Witness.linear .positive case_12_9_4, case_12_9_4_checked⟩

    · exact ⟨Witness.linear .negative case_12_9_5, case_12_9_5_checked⟩

  · have hkHi : k ≤ 6 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_12_10_1_checked⟩

    · exact ⟨Witness.rising, case_12_10_2_checked⟩

    · exact ⟨Witness.rising, case_12_10_3_checked⟩

    · exact ⟨Witness.linear .positive case_12_10_4, case_12_10_4_checked⟩

    · exact ⟨Witness.linear .positive case_12_10_5, case_12_10_5_checked⟩

    · exact ⟨Witness.linear .negative case_12_10_6, case_12_10_6_checked⟩

  · have hkHi : k ≤ 6 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_12_11_1_checked⟩

    · exact ⟨Witness.rising, case_12_11_2_checked⟩

    · exact ⟨Witness.rising, case_12_11_3_checked⟩

    · exact ⟨Witness.linear .positive case_12_11_4, case_12_11_4_checked⟩

    · exact ⟨Witness.linear .positive case_12_11_5, case_12_11_5_checked⟩

    · exact ⟨Witness.linear .negative case_12_11_6, case_12_11_6_checked⟩


#print axioms coverage_12
end ForestUnimodality.FiniteRows.FiniteData
