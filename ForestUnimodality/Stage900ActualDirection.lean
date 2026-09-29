import ForestUnimodality.Stage900DirectionInputsData.Case01
import ForestUnimodality.Stage900DirectionInputsData.Case02
import ForestUnimodality.Stage900DirectionInputsData.Case03
import ForestUnimodality.Stage900DirectionInputsData.Case04
import ForestUnimodality.Stage900DirectionInputsData.Case05
import ForestUnimodality.Stage900DirectionInputsData.Case23
import ForestUnimodality.Stage900DirectionInputsData.Case24
import ForestUnimodality.Stage900DirectionInputsData.Case25
import ForestUnimodality.Stage900DirectionInputsData.Case26
import ForestUnimodality.Stage900DirectionInputsData.Case27
import ForestUnimodality.Stage900DirectionInputsData.Case28
import ForestUnimodality.Stage900DirectionTable

/-! Actual stage-900 coefficient directions. All finite scalar obligations,
source bounds, tail bounds, gradient profiles and numeric endpoint budgets
are discharged in the imported, kernel-checked modules. -/
namespace ForestUnimodality.Stage900ActualDirection
open Set Stage900DirectionTable ReciprocalGradientBudget

def profile0 (i : Fin 11) : GradientProfile :=
  ![Stage900DirectionInputsData.Case01.profile0, Stage900DirectionInputsData.Case02.profile0, Stage900DirectionInputsData.Case03.profile0, Stage900DirectionInputsData.Case04.profile0, Stage900DirectionInputsData.Case05.profile0, Stage900DirectionInputsData.Case23.profile0, Stage900DirectionInputsData.Case24.profile0, Stage900DirectionInputsData.Case25.profile0, Stage900DirectionInputsData.Case26.profile0, Stage900DirectionInputsData.Case27.profile0, Stage900DirectionInputsData.Case28.profile0] i

def profile1 (i : Fin 11) : GradientProfile :=
  ![Stage900DirectionInputsData.Case01.profile1, Stage900DirectionInputsData.Case02.profile1, Stage900DirectionInputsData.Case03.profile1, Stage900DirectionInputsData.Case04.profile1, Stage900DirectionInputsData.Case05.profile1, Stage900DirectionInputsData.Case23.profile1, Stage900DirectionInputsData.Case24.profile1, Stage900DirectionInputsData.Case25.profile1, Stage900DirectionInputsData.Case26.profile1, Stage900DirectionInputsData.Case27.profile1, Stage900DirectionInputsData.Case28.profile1] i

variable {V : Type*} [DecidableEq V]

theorem actual_inputs (i : Fin 11) {G : SimpleGraph V} {S B : Finset V}
    {z : ℝ} (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z)
    (hG : G.IsAcyclic) (hn : 900 ≤ S.card)
    (hz : z ∈ Icc (row i).a (row i).b)
    (hrank : (S.card : ℝ)/4 ≤ hardCoreMean G S z)
    (hmean : hardCoreMean G S z = (k : ℝ)) :
    DirectionBudgetGraph.Inputs (row i) G S B z (hardCoreAvailableMean G S B z)
      k (profile0 i) (profile1 i) := by
  fin_cases i
  · exact Stage900DirectionInputsData.Case01.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage900DirectionInputsData.Case02.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage900DirectionInputsData.Case03.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage900DirectionInputsData.Case04.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage900DirectionInputsData.Case05.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage900DirectionInputsData.Case23.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage900DirectionInputsData.Case24.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage900DirectionInputsData.Case25.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage900DirectionInputsData.Case26.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage900DirectionInputsData.Case27.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage900DirectionInputsData.Case28.actual_inputs k hB hG hn hz hrank hmean

theorem left_upper (i : Fin 11) (hi : isLeft i = true) : (row i).b ≤ 1 := by
  fin_cases i <;> norm_num [isLeft, row,
    Stage900DirectionData.Case01.parameters,
    Stage900DirectionData.Case02.parameters,
    Stage900DirectionData.Case03.parameters,
    Stage900DirectionData.Case04.parameters,
    Stage900DirectionData.Case05.parameters,
    Stage900DirectionData.Case23.parameters,
    Stage900DirectionData.Case24.parameters,
    Stage900DirectionData.Case25.parameters,
    Stage900DirectionData.Case26.parameters,
    Stage900DirectionData.Case27.parameters,
    Stage900DirectionData.Case28.parameters] at *

theorem right_lower (i : Fin 11) (hi : isLeft i = false) : 1 ≤ (row i).a := by
  fin_cases i <;> norm_num [isLeft, row,
    Stage900DirectionData.Case01.parameters,
    Stage900DirectionData.Case02.parameters,
    Stage900DirectionData.Case03.parameters,
    Stage900DirectionData.Case04.parameters,
    Stage900DirectionData.Case05.parameters,
    Stage900DirectionData.Case23.parameters,
    Stage900DirectionData.Case24.parameters,
    Stage900DirectionData.Case25.parameters,
    Stage900DirectionData.Case26.parameters,
    Stage900DirectionData.Case27.parameters,
    Stage900DirectionData.Case28.parameters] at *

theorem actual_left_positive (i : Fin 11) (hi : isLeft i = true)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ} (k : ℕ)
    (hB : IsMaximumMarginalIndependentOn G S B z)
    (hG : G.IsAcyclic) (hn : 900 ≤ S.card) (hk : 1 ≤ k)
    (hz : z ∈ Icc (row i).a (row i).b)
    (hrank : (S.card : ℝ)/4 ≤ hardCoreMean G S z)
    (hmean : hardCoreMean G S z = (k : ℝ)) :
    0 < tiltedLeft (countIndependent G S) z (partitionFunction G S z) k :=
  DirectionBudgetGraph.actual_left_positive (row_valid i)
    (actual_inputs i k hB hG hn hz hrank hmean) hk (left_upper i hi)
    (bracket_positive i).le (mass_positive i).le
    (by simpa only [hi, ↓reduceIte] using margin_positive i)

theorem actual_right_positive (i : Fin 11) (hi : isLeft i = false)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ} (k : ℕ)
    (hB : IsMaximumMarginalIndependentOn G S B z)
    (hG : G.IsAcyclic) (hn : 900 ≤ S.card)
    (hz : z ∈ Icc (row i).a (row i).b)
    (hrank : (S.card : ℝ)/4 ≤ hardCoreMean G S z)
    (hmean : hardCoreMean G S z = (k : ℝ)) :
    0 < tiltedRight (countIndependent G S) z (partitionFunction G S z) k :=
  DirectionBudgetGraph.actual_right_positive (row_valid i)
    (actual_inputs i k hB hG hn hz hrank hmean) (right_lower i hi)
    (bracket_positive i).le (mass_positive i).le
    (by simpa only [hi, Bool.false_eq_true, ↓reduceIte] using margin_positive i)

theorem actual_left_coefficient_lt (i : Fin 11) (hi : isLeft i = true)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ} (k : ℕ)
    (hB : IsMaximumMarginalIndependentOn G S B z)
    (hG : G.IsAcyclic) (hn : 900 ≤ S.card) (hk : 1 ≤ k)
    (hz : z ∈ Icc (row i).a (row i).b)
    (hrank : (S.card : ℝ)/4 ≤ hardCoreMean G S z)
    (hmean : hardCoreMean G S z = (k : ℝ)) :
    countIndependent G S (k-1) < countIndependent G S k :=
  DirectionBudgetGraph.actual_left_coefficient_lt (row_valid i)
    (actual_inputs i k hB hG hn hz hrank hmean) hk (left_upper i hi)
    (bracket_positive i).le (mass_positive i).le
    (by simpa only [hi, ↓reduceIte] using margin_positive i)

theorem actual_right_coefficient_lt (i : Fin 11) (hi : isLeft i = false)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ} (k : ℕ)
    (hB : IsMaximumMarginalIndependentOn G S B z)
    (hG : G.IsAcyclic) (hn : 900 ≤ S.card)
    (hz : z ∈ Icc (row i).a (row i).b)
    (hrank : (S.card : ℝ)/4 ≤ hardCoreMean G S z)
    (hmean : hardCoreMean G S z = (k : ℝ)) :
    countIndependent G S (k+1) < countIndependent G S k :=
  DirectionBudgetGraph.actual_right_coefficient_lt (row_valid i)
    (actual_inputs i k hB hG hn hz hrank hmean) (right_lower i hi)
    (bracket_positive i).le (mass_positive i).le
    (by simpa only [hi, Bool.false_eq_true, ↓reduceIte] using margin_positive i)

/-- Activity in the complete left direction window forces strict ascent. -/
theorem left_window_coefficient_lt {G : SimpleGraph V} {S : Finset V}
    {z : ℝ} (k : ℕ) (hG : G.IsAcyclic) (hn : 900 ≤ S.card)
    (hzlo : (1/3 : ℝ) ≤ z) (hzhi : z ≤ (22/25 : ℝ))
    (hrank : (S.card : ℝ)/4 ≤ hardCoreMean G S z)
    (hmean : hardCoreMean G S z = (k : ℝ)) :
    countIndependent G S (k-1) < countIndependent G S k := by
  obtain ⟨i, hi, hlo, hhi⟩ := covers_left hzlo hzhi
  obtain ⟨B, hB⟩ := exists_maximumWeightedIndependentOn G S (hardCoreVertexMarginal G S z)
  have hnR : (900 : ℝ) ≤ S.card := by exact_mod_cast hn
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by linarith
  have hk : 1 ≤ k := by exact_mod_cast hkR
  exact actual_left_coefficient_lt i hi k hB hG hn hk ⟨hlo, hhi⟩ hrank hmean

/-- Activity in the complete right direction window forces strict descent. -/
theorem right_window_coefficient_lt {G : SimpleGraph V} {S : Finset V}
    {z : ℝ} (k : ℕ) (hG : G.IsAcyclic) (hn : 900 ≤ S.card)
    (hzlo : (57/50 : ℝ) ≤ z) (hzhi : z ≤ (9/4 : ℝ))
    (hrank : (S.card : ℝ)/4 ≤ hardCoreMean G S z)
    (hmean : hardCoreMean G S z = (k : ℝ)) :
    countIndependent G S (k+1) < countIndependent G S k := by
  obtain ⟨i, hi, hlo, hhi⟩ := covers_right hzlo hzhi
  obtain ⟨B, hB⟩ := exists_maximumWeightedIndependentOn G S (hardCoreVertexMarginal G S z)
  exact actual_right_coefficient_lt i hi k hB hG hn ⟨hlo, hhi⟩ hrank hmean

#print axioms actual_inputs
#print axioms actual_left_positive
#print axioms actual_right_positive
#print axioms left_window_coefficient_lt
#print axioms right_window_coefficient_lt
end ForestUnimodality.Stage900ActualDirection
