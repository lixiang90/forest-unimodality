import ForestUnimodality.AnalyticMeanAssembly
import ForestUnimodality.Stage900ActualDirection
import ForestUnimodality.Stage900ActualCurvature

/-! A complete, unconditional size-900 forest theorem. The only graph
assumptions are acyclicity and the vertex-count bound. Every mean, source,
Fourier, tail and finite scalar certificate is discharged by the imports.
This does not settle the remaining orders 61 through 899. -/
namespace ForestUnimodality

variable {V : Type*} [DecidableEq V]

theorem countIndependent_unimodal_of_card_ge900 (G : SimpleGraph V)
    (S : Finset V) (hG : G.IsAcyclic) (hn : 900 ≤ S.card) :
    WeaklyUnimodal (countIndependent G S) := by
  obtain ⟨I, hI⟩ := exists_maximumIndependentOn G S
  apply weaklyUnimodal_of_no_central_weak_valley (countIndependent G S)
    ((S.card + 3) / 4) ((S.card + 2 * I.card) / 6 + 1)
    (countIndependent_le_succ_of_quarter G hG S)
    (hI.countIndependent_succ_le_of_matching_tail hG)
  intro k hkL hkU hkpos hvalley
  obtain ⟨z, ⟨hz, hmean⟩, _⟩ := hI.existsUnique_central_activity hG k hkL hkU hkpos
  have hrank : (S.card : ℝ) / 4 ≤ hardCoreMean G S z := by
    have hk : S.card ≤ 4 * k := by omega
    have hkR : (S.card : ℝ) ≤ 4 * (k : ℝ) := by exact_mod_cast hk
    rw [hmean]
    linarith
  by_cases hleft : z ≤ (22 / 25 : ℝ)
  · exact (not_lt_of_ge hvalley.1)
      (Stage900ActualDirection.left_window_coefficient_lt k hG hn hz.1 hleft hrank hmean)
  · by_cases hright : (57 / 50 : ℝ) ≤ z
    · exact (not_lt_of_ge hvalley.2)
        (Stage900ActualDirection.right_window_coefficient_lt k hG hn hright hz.2.le hrank hmean)
    · have hc := Stage900ActualCurvature.central_window_positive k hG hn
        (le_of_not_ge hleft) (le_of_not_ge hright) hrank hmean
      have hz0 : 0 < z := lt_of_lt_of_le (by norm_num) hz.1
      have hZ : 0 < partitionFunction G S z := partitionFunction_pos G S hz0.le
      have hnonpos := (tilted_kernels_nonpositive_of_weak_valley (countIndependent G S)
        hz0 hZ hkpos hvalley.1 hvalley.2).2.2
      exact (not_lt_of_ge hnonpos) hc

#print axioms countIndependent_unimodal_of_card_ge900

end ForestUnimodality
