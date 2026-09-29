import ForestUnimodality.Stage170Geometry.Batch030_039
import ForestUnimodality.Stage350ParentHandoff

namespace ForestUnimodality.Stage170Windows.Strip039
open Stage170Geometry
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem actual_finite_cover_or_no_weak_valley {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 170≤S.card) (hz : 0<z) (hk : 1≤k)
    (hq : z/(1+z)∈Set.Icc ((2983/6208):ℝ) ((4487/9312):ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k) :
    (∃i : Fin 558, i∈([467,381,133,134,135,136,137] : List (Fin 558)) ∧
      (rectangle i).Contains (z/(1+z)) (hardCoreAvailableMean G S B z)) ∨
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  have hS : 0<S.card := by omega
  have hqs : z/(1+z)∈Set.Icc ((strip 39).qlo:ℝ) ((strip 39).qhi:ℝ) := by
    change z/(1+z)∈Set.Icc (((2983/6208):ℚ):ℝ) (((4487/9312):ℚ):ℝ)
    norm_num
    exact hq
  have hlo := (strip 39).actual_mean_lower (window 39) 170
    Stage170SourceData.Window088.valid source039_checked hB hG hz hn hqs hrank
  by_cases hhi : hardCoreAvailableMean G S B z≤((strip 39).mhi:ℝ)
  · obtain ⟨i,hi,hpoint⟩ := (strip 39).check_sound rectangle strip039_checked hqs ⟨hlo,hhi⟩
    exact Or.inl ⟨i,hi,hpoint⟩
  · have hp := (strip 39).parent_domain (window 39) 170
      Stage170SourceData.Window088.valid source039_checked hz hqs (le_of_not_ge hhi)
    exact Or.inr (Stage350ParentHandoff.no_weak_valley (window 39).parent
      k hB hG hS hp.2 hp.1 hrank hmean hk)

#print axioms actual_finite_cover_or_no_weak_valley
end ForestUnimodality.Stage170Windows.Strip039
