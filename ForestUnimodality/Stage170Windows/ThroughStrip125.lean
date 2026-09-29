import ForestUnimodality.Stage170Windows.ThroughStrip124
import ForestUnimodality.Stage170Windows.Strip125.Complete

/-! Reuse a checked interval theorem; all graph and mean premises remain. -/
namespace ForestUnimodality.Stage170Windows.ThroughStrip125
variable {V : Type*} [DecidableEq V]

theorem no_weak_valley {G : SimpleGraph V} {S : Finset V} {z : ℝ}
    (k : ℕ) (hG : G.IsAcyclic) (hn : 170≤S.card) (hN : S.card≤349) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (1/4:ℝ) (2/3:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  by_cases h124 : z/(1+z)≤(83/126:ℝ)
  · exact ThroughStrip124.no_weak_valley k hG hn hN hz
      ⟨hq.1,h124⟩ hrank hmean
  exact Strip125.no_weak_valley k hG hn hN hz
    ⟨(lt_of_not_ge h124).le,hq.2⟩ hrank hmean

#print axioms no_weak_valley
end ForestUnimodality.Stage170Windows.ThroughStrip125
