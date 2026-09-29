import ForestUnimodality.FiniteWitness
import Mathlib.Tactic.IntervalCases

/-! Generated candidate witnesses. Each sign is rechecked by the Lean kernel.
The coverage theorem quantifies over Domain, independently of this record list.
Source and integer-witness hashes are recorded in research/finite-integer-witnesses/manifest.json.
-/
namespace ForestUnimodality.FiniteRows.FiniteData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_10_5_1_checked :
    (Witness.rising).check 10 5 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_10_5_2_checked :
    (Witness.rising).check 10 5 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_10_6_1_checked :
    (Witness.rising).check 10 6 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_10_6_2_checked :
    (Witness.rising).check 10 6 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_10_6_3_checked :
    (Witness.rising).check 10 6 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_10_7_1_checked :
    (Witness.rising).check 10 7 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_10_7_2_checked :
    (Witness.rising).check 10 7 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_10_7_3_checked :
    (Witness.rising).check 10 7 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_10_7_4 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 2] }

theorem case_10_7_4_checked :
    (Witness.linear .negative case_10_7_4).check 10 7 4 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_10_8_1_checked :
    (Witness.rising).check 10 8 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_10_8_2_checked :
    (Witness.rising).check 10 8 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_10_8_3_checked :
    (Witness.rising).check 10 8 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_10_8_4 : Certificate := {
  objectiveScale := 1
  eta := 2
  rows := #[]
  caps := #[0, 0, 1] }

theorem case_10_8_4_checked :
    (Witness.linear .positive case_10_8_4).check 10 8 4 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_10_9_1_checked :
    (Witness.rising).check 10 9 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_10_9_2_checked :
    (Witness.rising).check 10 9 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_10_9_3_checked :
    (Witness.rising).check 10 9 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_10_9_4 : Certificate := {
  objectiveScale := 1
  eta := 2
  rows := #[]
  caps := #[0, 0] }

theorem case_10_9_4_checked :
    (Witness.linear .positive case_10_9_4).check 10 9 4 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_10_9_5 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_10_9_5_checked :
    (Witness.linear .negative case_10_9_5).check 10 9 5 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_10 (a k : ℕ) (h : Domain 10 a k) :
    ∃ w : Witness, w.check 10 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 5 ≤ a := by omega
  have haHi : a ≤ 9 := by omega
  interval_cases a

  · have hkHi : k ≤ 2 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_10_5_1_checked⟩

    · exact ⟨Witness.rising, case_10_5_2_checked⟩

  · have hkHi : k ≤ 3 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_10_6_1_checked⟩

    · exact ⟨Witness.rising, case_10_6_2_checked⟩

    · exact ⟨Witness.rising, case_10_6_3_checked⟩

  · have hkHi : k ≤ 4 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_10_7_1_checked⟩

    · exact ⟨Witness.rising, case_10_7_2_checked⟩

    · exact ⟨Witness.rising, case_10_7_3_checked⟩

    · exact ⟨Witness.linear .negative case_10_7_4, case_10_7_4_checked⟩

  · have hkHi : k ≤ 4 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_10_8_1_checked⟩

    · exact ⟨Witness.rising, case_10_8_2_checked⟩

    · exact ⟨Witness.rising, case_10_8_3_checked⟩

    · exact ⟨Witness.linear .positive case_10_8_4, case_10_8_4_checked⟩

  · have hkHi : k ≤ 5 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_10_9_1_checked⟩

    · exact ⟨Witness.rising, case_10_9_2_checked⟩

    · exact ⟨Witness.rising, case_10_9_3_checked⟩

    · exact ⟨Witness.linear .positive case_10_9_4, case_10_9_4_checked⟩

    · exact ⟨Witness.linear .negative case_10_9_5, case_10_9_5_checked⟩


#print axioms coverage_10
end ForestUnimodality.FiniteRows.FiniteData
