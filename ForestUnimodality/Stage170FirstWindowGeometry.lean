import ForestUnimodality.Stage170Geometry.Batch000_009
import ForestUnimodality.Stage350PlainAllOrders

namespace ForestUnimodality.Stage170FirstWindow
open Stage170Geometry
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem actual_finite_cover_or_left_growth {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z)
    (hG : G.IsAcyclic) (hn : 170 ≤ S.card)
    (hz : 0 < z) (hk : 1 ≤ k)
    (hq : z / (1 + z) ∈ Set.Icc (1/4 : ℝ) (9/35 : ℝ))
    (hrank : (S.card : ℝ) / 4 ≤ hardCoreMean G S z)
    (hmean : hardCoreMean G S z = k) :
    (∃ i : Fin 558, i∈([428,349,0,1,2,3] : List (Fin 558)) ∧
      (rectangle i).Contains (z/(1+z)) (hardCoreAvailableMean G S B z)) ∨
    countIndependent G S (k-1) < countIndependent G S k := by
  have hS : 0 < S.card := by omega
  have hqs : z/(1+z)∈Set.Icc ((strip 0).qlo:ℝ) ((strip 0).qhi:ℝ) := by
    change z/(1+z)∈Set.Icc ((1/4:ℚ):ℝ) ((9/35:ℚ):ℝ)
    norm_num
    exact hq
  have hlo := (strip 0).actual_mean_lower (window 0) 170
    (Stage170SourceData.Window000.valid) source000_checked hB hG hz hn hqs hrank
  by_cases hhi : hardCoreAvailableMean G S B z ≤ ((strip 0).mhi:ℝ)
  · obtain ⟨i, hi, hpoint⟩ := (strip 0).check_sound rectangle strip000_checked hqs ⟨hlo,hhi⟩
    exact Or.inl ⟨i, hi, hpoint⟩
  · have hparent := (strip 0).parent_domain (window 0) 170
      Stage170SourceData.Window000.valid source000_checked hz hqs (le_of_not_ge hhi)
    apply Or.inr
    apply Stage350PlainAllOrders.actual_left_coefficient_lt 0 (by decide +kernel)
      k hB hG hS _ _ hrank hmean hk
    · rw [Stage350PlainAllOrders.source_start_eq]
      exact hparent.2
    · change z∈Set.Icc (1/3:ℝ) (2/5:ℝ)
      have hl := (le_div_iff₀ (by positivity : 0<1+z)).mp hq.1
      have hu := (div_le_iff₀ (by positivity : 0<1+z)).mp hq.2
      constructor <;> linarith

#print axioms actual_finite_cover_or_left_growth
end ForestUnimodality.Stage170FirstWindow
