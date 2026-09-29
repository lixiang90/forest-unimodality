import ForestUnimodality.AnalyticMeanAssembly
import ForestUnimodality.Stage350PlainActualDirection
import ForestUnimodality.Stage350JointActualDirection
import ForestUnimodality.Stage350ActualCurvature

/-! Unconditional weak unimodality for every forest of order at least 350.
The five closed activity windows cover the entire mean-matched central
range. All source, moment, tail and numerical premises are discharged by
the imported theorems. -/
namespace ForestUnimodality

variable {V : Type*} [DecidableEq V]

theorem countIndependent_unimodal_of_card_ge350 (G : SimpleGraph V)
    (S : Finset V) (hG : G.IsAcyclic) (hn : 350 ≤ S.card) :
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
  by_cases hleft : z ≤ (7 / 10 : ℝ)
  · exact (not_lt_of_ge hvalley.1)
      (Stage350PlainActualDirection.left_window_coefficient_lt k hG hn hz.1 hleft hrank hmean)
  · by_cases hjleft : z ≤ (22 / 25 : ℝ)
    · exact (not_lt_of_ge hvalley.1)
        (Stage350JointActualDirection.left_window_coefficient_lt k hG hn
          ⟨le_of_not_ge hleft, hjleft⟩ hrank hmean)
    · by_cases hright : (7 / 5 : ℝ) ≤ z
      · exact (not_lt_of_ge hvalley.2)
          (Stage350PlainActualDirection.right_window_coefficient_lt k hG hn
            hright hz.2.le hrank hmean)
      · by_cases hjright : (57 / 50 : ℝ) ≤ z
        · exact (not_lt_of_ge hvalley.2)
            (Stage350JointActualDirection.right_window_coefficient_lt k hG hn
              ⟨hjright, le_of_not_ge hright⟩ hrank hmean)
        · have hc := Stage350ActualCurvature.central_window_positive k hG hn
            (le_of_not_ge hjleft) (le_of_not_ge hjright) hrank hmean
          have hz0 : 0 < z := lt_of_lt_of_le (by norm_num) hz.1
          have hZ : 0 < partitionFunction G S z := partitionFunction_pos G S hz0.le
          have hnonpos := (tilted_kernels_nonpositive_of_weak_valley (countIndependent G S)
            hz0 hZ hkpos hvalley.1 hvalley.2).2.2
          exact (not_lt_of_ge hnonpos) hc

#print axioms countIndependent_unimodal_of_card_ge350

end ForestUnimodality
