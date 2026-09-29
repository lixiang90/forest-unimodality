import ForestUnimodality.Stage350PlainAllOrders
import ForestUnimodality.Stage350JointActualDirection
import ForestUnimodality.Stage350ActualCurvature

/-! The complete 43-row analytic handoff, with no lower bound on graph
order beyond nonemptiness. Finite stages may use this when the actual
available mean lies above their parent's certified starting point. -/
namespace ForestUnimodality.Stage350ParentHandoff
open Set

theorem plain_a (i : Fin 11) :
    (Stage350PlainDirectionTable.row i).a =
      ((Stage350SourceTable.row (Stage350PlainDirectionTable.sourceIndex i)).a : ℝ) := by
  fin_cases i
  · exact Stage350PlainInputsData.Case01.scalar_valid.a_match
  · exact Stage350PlainInputsData.Case02.scalar_valid.a_match
  · exact Stage350PlainInputsData.Case03.scalar_valid.a_match
  · exact Stage350PlainInputsData.Case36.scalar_valid.a_match
  · exact Stage350PlainInputsData.Case37.scalar_valid.a_match
  · exact Stage350PlainInputsData.Case38.scalar_valid.a_match
  · exact Stage350PlainInputsData.Case39.scalar_valid.a_match
  · exact Stage350PlainInputsData.Case40.scalar_valid.a_match
  · exact Stage350PlainInputsData.Case41.scalar_valid.a_match
  · exact Stage350PlainInputsData.Case42.scalar_valid.a_match
  · exact Stage350PlainInputsData.Case43.scalar_valid.a_match

theorem plain_b (i : Fin 11) :
    (Stage350PlainDirectionTable.row i).b =
      ((Stage350SourceTable.row (Stage350PlainDirectionTable.sourceIndex i)).b : ℝ) := by
  fin_cases i
  · exact Stage350PlainInputsData.Case01.scalar_valid.b_match
  · exact Stage350PlainInputsData.Case02.scalar_valid.b_match
  · exact Stage350PlainInputsData.Case03.scalar_valid.b_match
  · exact Stage350PlainInputsData.Case36.scalar_valid.b_match
  · exact Stage350PlainInputsData.Case37.scalar_valid.b_match
  · exact Stage350PlainInputsData.Case38.scalar_valid.b_match
  · exact Stage350PlainInputsData.Case39.scalar_valid.b_match
  · exact Stage350PlainInputsData.Case40.scalar_valid.b_match
  · exact Stage350PlainInputsData.Case41.scalar_valid.b_match
  · exact Stage350PlainInputsData.Case42.scalar_valid.b_match
  · exact Stage350PlainInputsData.Case43.scalar_valid.b_match

theorem central_a (i : Fin 17) :
    (Stage350CurvatureTable.row i).a =
      ((Stage350SourceTable.row (Stage350CurvatureTable.sourceIndex i)).a : ℝ) := by
  fin_cases i
  · exact Stage350CurvatureInputsData.Case07.scalar_valid.a_match
  · exact Stage350CurvatureInputsData.Case08.scalar_valid.a_match
  · exact Stage350CurvatureInputsData.Case09.scalar_valid.a_match
  · exact Stage350CurvatureInputsData.Case10.scalar_valid.a_match
  · exact Stage350CurvatureInputsData.Case11.scalar_valid.a_match
  · exact Stage350CurvatureInputsData.Case12.scalar_valid.a_match
  · exact Stage350CurvatureInputsData.Case13.scalar_valid.a_match
  · exact Stage350CurvatureInputsData.Case14.scalar_valid.a_match
  · exact Stage350CurvatureInputsData.Case15.scalar_valid.a_match
  · exact Stage350CurvatureInputsData.Case16.scalar_valid.a_match
  · exact Stage350CurvatureInputsData.Case17.scalar_valid.a_match
  · exact Stage350CurvatureInputsData.Case18.scalar_valid.a_match
  · exact Stage350CurvatureInputsData.Case19.scalar_valid.a_match
  · exact Stage350CurvatureInputsData.Case20.scalar_valid.a_match
  · exact Stage350CurvatureInputsData.Case21.scalar_valid.a_match
  · exact Stage350CurvatureInputsData.Case22.scalar_valid.a_match
  · exact Stage350CurvatureInputsData.Case23.scalar_valid.a_match

theorem central_b (i : Fin 17) :
    (Stage350CurvatureTable.row i).b =
      ((Stage350SourceTable.row (Stage350CurvatureTable.sourceIndex i)).b : ℝ) := by
  fin_cases i
  · exact Stage350CurvatureInputsData.Case07.scalar_valid.b_match
  · exact Stage350CurvatureInputsData.Case08.scalar_valid.b_match
  · exact Stage350CurvatureInputsData.Case09.scalar_valid.b_match
  · exact Stage350CurvatureInputsData.Case10.scalar_valid.b_match
  · exact Stage350CurvatureInputsData.Case11.scalar_valid.b_match
  · exact Stage350CurvatureInputsData.Case12.scalar_valid.b_match
  · exact Stage350CurvatureInputsData.Case13.scalar_valid.b_match
  · exact Stage350CurvatureInputsData.Case14.scalar_valid.b_match
  · exact Stage350CurvatureInputsData.Case15.scalar_valid.b_match
  · exact Stage350CurvatureInputsData.Case16.scalar_valid.b_match
  · exact Stage350CurvatureInputsData.Case17.scalar_valid.b_match
  · exact Stage350CurvatureInputsData.Case18.scalar_valid.b_match
  · exact Stage350CurvatureInputsData.Case19.scalar_valid.b_match
  · exact Stage350CurvatureInputsData.Case20.scalar_valid.b_match
  · exact Stage350CurvatureInputsData.Case21.scalar_valid.b_match
  · exact Stage350CurvatureInputsData.Case22.scalar_valid.b_match
  · exact Stage350CurvatureInputsData.Case23.scalar_valid.b_match

theorem central_start (i : Fin 17) :
    (Stage350CurvatureTable.row i).start =
      ((Stage350SourceTable.row (Stage350CurvatureTable.sourceIndex i)).start : ℝ) := by
  fin_cases i
  · exact Stage350CurvatureInputsData.Case07.scalar_valid.start_match
  · exact Stage350CurvatureInputsData.Case08.scalar_valid.start_match
  · exact Stage350CurvatureInputsData.Case09.scalar_valid.start_match
  · exact Stage350CurvatureInputsData.Case10.scalar_valid.start_match
  · exact Stage350CurvatureInputsData.Case11.scalar_valid.start_match
  · exact Stage350CurvatureInputsData.Case12.scalar_valid.start_match
  · exact Stage350CurvatureInputsData.Case13.scalar_valid.start_match
  · exact Stage350CurvatureInputsData.Case14.scalar_valid.start_match
  · exact Stage350CurvatureInputsData.Case15.scalar_valid.start_match
  · exact Stage350CurvatureInputsData.Case16.scalar_valid.start_match
  · exact Stage350CurvatureInputsData.Case17.scalar_valid.start_match
  · exact Stage350CurvatureInputsData.Case18.scalar_valid.start_match
  · exact Stage350CurvatureInputsData.Case19.scalar_valid.start_match
  · exact Stage350CurvatureInputsData.Case20.scalar_valid.start_match
  · exact Stage350CurvatureInputsData.Case21.scalar_valid.start_match
  · exact Stage350CurvatureInputsData.Case22.scalar_valid.start_match
  · exact Stage350CurvatureInputsData.Case23.scalar_valid.start_match

theorem sources_cover (i : Fin 43) :
    (∃ j : Fin 11, Stage350PlainDirectionTable.sourceIndex j = i) ∨
    (∃ j : Fin 15, Stage350JointDirectionTable.sourceIndex j = i) ∨
    (∃ j : Fin 17, Stage350CurvatureTable.sourceIndex j = i) := by
  revert i
  decide

variable {V : Type*} [DecidableEq V]

theorem no_weak_valley (i : Fin 43)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ} (k : ℕ)
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 0 < S.card)
    (hstart : ((Stage350SourceTable.row i).start : ℝ) ≤ hardCoreAvailableMean G S B z)
    (hz : z ∈ Icc ((Stage350SourceTable.row i).a : ℝ) (Stage350SourceTable.row i).b)
    (hrank : (S.card : ℝ) / 4 ≤ hardCoreMean G S z)
    (hmean : hardCoreMean G S z = k) (hk : 1 ≤ k) :
    ¬ (countIndependent G S k ≤ countIndependent G S (k-1) ∧
      countIndependent G S k ≤ countIndependent G S (k+1)) := by
  rcases sources_cover i with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · apply Stage350PlainAllOrders.no_weak_valley_of_start j k hB hG hn
    · simpa only [Stage350PlainAllOrders.source_start_eq] using hstart
    · simpa only [plain_a, plain_b] using hz
    · exact hrank
    · exact hmean
    · exact hk
  · have hs : (Stage350JointDirectionTable.row j).start ≤ hardCoreAvailableMean G S B z := by
      simpa only [Stage350JointDirectionTable.start_match] using hstart
    intro hv
    cases hj : Stage350JointDirectionTable.reverse j with
    | true =>
        exact (not_lt_of_ge hv.1)
          (Stage350JointActualDirection.left_coefficient_of_start j hj k hB hG hn hs hz.1 hz.2 hrank hmean)
    | false =>
        exact (not_lt_of_ge hv.2)
          (Stage350JointActualDirection.right_coefficient_of_start j hj k hB hG hn hs hz.1 hz.2 hrank hmean)
  · have hs : (Stage350CurvatureTable.row j).start ≤ hardCoreAvailableMean G S B z := by
      simpa only [central_start] using hstart
    have hzj : z ∈ Icc (Stage350CurvatureTable.row j).a (Stage350CurvatureTable.row j).b := by
      simpa only [central_a, central_b] using hz
    have hc := Stage350ActualCurvature.actual_positive_any_size j k hB hG hn hk hzj hrank hmean hs
    have ha : (0 : ℝ) < (Stage350SourceTable.row (Stage350CurvatureTable.sourceIndex j)).a := by
      exact_mod_cast (Stage350SourceTable.valid (Stage350CurvatureTable.sourceIndex j)).a_pos
    have hz0 : 0 < z := ha.trans_le hz.1
    intro hv
    have hnonpos := (tilted_kernels_nonpositive_of_weak_valley (countIndependent G S)
      hz0 (partitionFunction_pos G S hz0.le) hk hv.1 hv.2).2.2
    exact (not_lt_of_ge hnonpos) hc

#print axioms sources_cover
#print axioms no_weak_valley
end ForestUnimodality.Stage350ParentHandoff

