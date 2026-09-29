import ForestUnimodality.Stage170Windows.ThroughStrip110
import ForestUnimodality.Stage170Windows.Strip111.Complete
import ForestUnimodality.Stage170Windows.Strip112.Complete

/-! Reuse a checked interval theorem; all graph and mean premises remain. -/
namespace ForestUnimodality.Stage170Windows.ThroughStrip112
variable {V : Type*} [DecidableEq V]

theorem no_weak_valley {G : SimpleGraph V} {S : Finset V} {z : ℝ}
    (k : ℕ) (hG : G.IsAcyclic) (hn : 170≤S.card) (hN : S.card≤349) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (1/4:ℝ) (7/12:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  by_cases h110 : z/(1+z)≤(27/47:ℝ)
  · exact ThroughStrip110.no_weak_valley k hG hn hN hz
      ⟨hq.1,h110⟩ hrank hmean
  by_cases h111 : z/(1+z)≤(653/1128:ℝ)
  · exact Strip111.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h110).le,h111⟩ hrank hmean
  exact Strip112.no_weak_valley k hG hn hN hz
    ⟨(lt_of_not_ge h111).le,hq.2⟩ hrank hmean

#print axioms no_weak_valley
end ForestUnimodality.Stage170Windows.ThroughStrip112
