import ForestUnimodality.BridgeFirstActivity
import ForestUnimodality.BridgeSecondActivity

/-! Actual coefficient growth on the first two adjoining activity intervals.
This remains an activity-restricted result, not all-order unimodality. -/
namespace ForestUnimodality.BridgeInitialActivity
variable {V : Type*} [DecidableEq V]

theorem left_window_coefficient_lt {G : SimpleGraph V} {S : Finset V} {z : ℝ}
    (k : ℕ) (hG : G.IsAcyclic) (hn : 59≤S.card) (hN : S.card≤349) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (1/4:ℝ) (37/140:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k) :
    countIndependent G S (k-1)<countIndependent G S k := by
  by_cases h : z/(1+z)≤(9/35:ℝ)
  · exact BridgeFirstActivity.left_window_coefficient_lt k hG hn hN hz ⟨hq.1,h⟩ hrank hmean
  · exact BridgeSecondActivity.left_window_coefficient_lt k hG hn hN hz
      ⟨(lt_of_not_ge h).le,hq.2⟩ hrank hmean

theorem no_weak_valley {G : SimpleGraph V} {S : Finset V} {z : ℝ}
    (k : ℕ) (hG : G.IsAcyclic) (hn : 59≤S.card) (hN : S.card≤349) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (1/4:ℝ) (37/140:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  have hh := left_window_coefficient_lt k hG hn hN hz hq hrank hmean
  rintro ⟨hl,_⟩
  exact (not_le_of_gt hh) hl

#print axioms left_window_coefficient_lt
#print axioms no_weak_valley
end ForestUnimodality.BridgeInitialActivity
