import ForestUnimodality.Stage170Geometry.Batch020_029
import ForestUnimodality.Stage350ParentHandoff

namespace ForestUnimodality.Stage170Windows.Strip024
open Stage170Geometry
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem actual_finite_cover_or_no_weak_valley {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 170≤S.card) (hz : 0<z) (hk : 1≤k)
    (hq : z/(1+z)∈Set.Icc ((22/51):ℝ) ((67/153):ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k) :
    (∃i : Fin 558, i∈([452,373,96,97,98,99] : List (Fin 558)) ∧
      (rectangle i).Contains (z/(1+z)) (hardCoreAvailableMean G S B z)) ∨
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  have hS : 0<S.card := by omega
  have hqs : z/(1+z)∈Set.Icc ((strip 24).qlo:ℝ) ((strip 24).qhi:ℝ) := by
    change z/(1+z)∈Set.Icc (((22/51):ℚ):ℝ) (((67/153):ℚ):ℝ)
    norm_num
    exact hq
  have hlo := (strip 24).actual_mean_lower (window 24) 170
    Stage170SourceData.Window024.valid source024_checked hB hG hz hn hqs hrank
  by_cases hhi : hardCoreAvailableMean G S B z≤((strip 24).mhi:ℝ)
  · obtain ⟨i,hi,hpoint⟩ := (strip 24).check_sound rectangle strip024_checked hqs ⟨hlo,hhi⟩
    exact Or.inl ⟨i,hi,hpoint⟩
  · have hp := (strip 24).parent_domain (window 24) 170
      Stage170SourceData.Window024.valid source024_checked hz hqs (le_of_not_ge hhi)
    exact Or.inr (Stage350ParentHandoff.no_weak_valley (window 24).parent
      k hB hG hS hp.2 hp.1 hrank hmean hk)

#print axioms actual_finite_cover_or_no_weak_valley
end ForestUnimodality.Stage170Windows.Strip024
