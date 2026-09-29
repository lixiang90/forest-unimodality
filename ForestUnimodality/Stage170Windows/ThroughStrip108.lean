import ForestUnimodality.Stage170Windows.ThroughStrip106
import ForestUnimodality.Stage170Windows.Strip107.Complete
import ForestUnimodality.Stage170Windows.Strip108.Complete

/-! Reuse a checked interval theorem; all graph and mean premises remain. -/
namespace ForestUnimodality.Stage170Windows.ThroughStrip108
variable {V : Type*} [DecidableEq V]

theorem no_weak_valley {G : SimpleGraph V} {S : Finset V} {z : ℝ}
    (k : ℕ) (hG : G.IsAcyclic) (hn : 170≤S.card) (hN : S.card≤349) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (1/4:ℝ) (53/93:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  by_cases h106 : z/(1+z)≤(13/23:ℝ)
  · exact ThroughStrip106.no_weak_valley k hG hn hN hz
      ⟨hq.1,h106⟩ hrank hmean
  by_cases h107 : z/(1+z)≤(21/37:ℝ)
  · exact Strip107.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h106).le,h107⟩ hrank hmean
  exact Strip108.no_weak_valley k hG hn hN hz
    ⟨(lt_of_not_ge h107).le,hq.2⟩ hrank hmean

#print axioms no_weak_valley
end ForestUnimodality.Stage170Windows.ThroughStrip108
