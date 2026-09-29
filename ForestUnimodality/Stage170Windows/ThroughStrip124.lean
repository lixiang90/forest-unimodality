import ForestUnimodality.Stage170Windows.ThroughStrip123
import ForestUnimodality.Stage170Windows.Strip124.Complete

/-! Reuse a checked interval theorem; all graph and mean premises remain. -/
namespace ForestUnimodality.Stage170Windows.ThroughStrip124
variable {V : Type*} [DecidableEq V]

theorem no_weak_valley {G : SimpleGraph V} {S : Finset V} {z : ℝ}
    (k : ℕ) (hG : G.IsAcyclic) (hn : 170≤S.card) (hN : S.card≤349) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (1/4:ℝ) (83/126:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  by_cases h123 : z/(1+z)≤(41/63:ℝ)
  · exact ThroughStrip123.no_weak_valley k hG hn hN hz
      ⟨hq.1,h123⟩ hrank hmean
  exact Strip124.no_weak_valley k hG hn hN hz
    ⟨(lt_of_not_ge h123).le,hq.2⟩ hrank hmean

#print axioms no_weak_valley
end ForestUnimodality.Stage170Windows.ThroughStrip124
