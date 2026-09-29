import ForestUnimodality.Stage170Windows.ThroughStrip112
import ForestUnimodality.Stage170Windows.Strip113.Complete
import ForestUnimodality.Stage170Windows.Strip114.Complete
import ForestUnimodality.Stage170Windows.Strip115.Complete

/-! Reuse a checked interval theorem; all graph and mean premises remain. -/
namespace ForestUnimodality.Stage170Windows.ThroughStrip115
variable {V : Type*} [DecidableEq V]

theorem no_weak_valley {G : SimpleGraph V} {S : Finset V} {z : ℝ}
    (k : ℕ) (hG : G.IsAcyclic) (hn : 170≤S.card) (hN : S.card≤349) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (1/4:ℝ) (3/5:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  by_cases h112 : z/(1+z)≤(7/12:ℝ)
  · exact ThroughStrip112.no_weak_valley k hG hn hN hz
      ⟨hq.1,h112⟩ hrank hmean
  by_cases h113 : z/(1+z)≤(53/90:ℝ)
  · exact Strip113.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h112).le,h113⟩ hrank hmean
  by_cases h114 : z/(1+z)≤(107/180:ℝ)
  · exact Strip114.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h113).le,h114⟩ hrank hmean
  exact Strip115.no_weak_valley k hG hn hN hz
    ⟨(lt_of_not_ge h114).le,hq.2⟩ hrank hmean

#print axioms no_weak_valley
end ForestUnimodality.Stage170Windows.ThroughStrip115
