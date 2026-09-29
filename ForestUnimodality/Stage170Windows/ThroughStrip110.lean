import ForestUnimodality.Stage170Windows.ThroughStrip108
import ForestUnimodality.Stage170Windows.Strip109.Complete
import ForestUnimodality.Stage170Windows.Strip110.Complete

/-! Reuse a checked interval theorem; all graph and mean premises remain. -/
namespace ForestUnimodality.Stage170Windows.ThroughStrip110
variable {V : Type*} [DecidableEq V]

theorem no_weak_valley {G : SimpleGraph V} {S : Finset V} {z : ℝ}
    (k : ℕ) (hG : G.IsAcyclic) (hn : 170≤S.card) (hN : S.card≤349) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (1/4:ℝ) (27/47:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  by_cases h108 : z/(1+z)≤(53/93:ℝ)
  · exact ThroughStrip108.no_weak_valley k hG hn hN hz
      ⟨hq.1,h108⟩ hrank hmean
  by_cases h109 : z/(1+z)≤(107/187:ℝ)
  · exact Strip109.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h108).le,h109⟩ hrank hmean
  exact Strip110.no_weak_valley k hG hn hN hz
    ⟨(lt_of_not_ge h109).le,hq.2⟩ hrank hmean

#print axioms no_weak_valley
end ForestUnimodality.Stage170Windows.ThroughStrip110
