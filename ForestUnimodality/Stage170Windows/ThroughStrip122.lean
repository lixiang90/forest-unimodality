import ForestUnimodality.Stage170Windows.ThroughStrip119
import ForestUnimodality.Stage170Windows.Strip120.Complete
import ForestUnimodality.Stage170Windows.Strip121.Complete
import ForestUnimodality.Stage170Windows.Strip122.Complete

/-! Reuse a checked interval theorem; all graph and mean premises remain. -/
namespace ForestUnimodality.Stage170Windows.ThroughStrip122
variable {V : Type*} [DecidableEq V]

theorem no_weak_valley {G : SimpleGraph V} {S : Finset V} {z : ℝ}
    (k : ℕ) (hG : G.IsAcyclic) (hn : 170≤S.card) (hN : S.card≤349) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (1/4:ℝ) (9/14:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  by_cases h119 : z/(1+z)≤(33/53:ℝ)
  · exact ThroughStrip119.no_weak_valley k hG hn hN hz
      ⟨hq.1,h119⟩ hrank hmean
  by_cases h120 : z/(1+z)≤(467/742:ℝ)
  · exact Strip120.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h119).le,h120⟩ hrank hmean
  by_cases h121 : z/(1+z)≤(236/371:ℝ)
  · exact Strip121.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h120).le,h121⟩ hrank hmean
  exact Strip122.no_weak_valley k hG hn hN hz
    ⟨(lt_of_not_ge h121).le,hq.2⟩ hrank hmean

#print axioms no_weak_valley
end ForestUnimodality.Stage170Windows.ThroughStrip122
