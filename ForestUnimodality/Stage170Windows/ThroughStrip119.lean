import ForestUnimodality.Stage170Windows.ThroughStrip115
import ForestUnimodality.Stage170Windows.Strip116.Complete
import ForestUnimodality.Stage170Windows.Strip117.Complete
import ForestUnimodality.Stage170Windows.Strip118.Complete
import ForestUnimodality.Stage170Windows.Strip119.Complete

/-! Reuse a checked interval theorem; all graph and mean premises remain. -/
namespace ForestUnimodality.Stage170Windows.ThroughStrip119
variable {V : Type*} [DecidableEq V]

theorem no_weak_valley {G : SimpleGraph V} {S : Finset V} {z : ℝ}
    (k : ℕ) (hG : G.IsAcyclic) (hn : 170≤S.card) (hN : S.card≤349) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (1/4:ℝ) (33/53:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  by_cases h115 : z/(1+z)≤(3/5:ℝ)
  · exact ThroughStrip115.no_weak_valley k hG hn hN hz
      ⟨hq.1,h115⟩ hrank hmean
  by_cases h116 : z/(1+z)≤(123/203:ℝ)
  · exact Strip116.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h115).le,h116⟩ hrank hmean
  by_cases h117 : z/(1+z)≤(63/103:ℝ)
  · exact Strip117.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h116).le,h117⟩ hrank hmean
  by_cases h118 : z/(1+z)≤(129/209:ℝ)
  · exact Strip118.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h117).le,h118⟩ hrank hmean
  exact Strip119.no_weak_valley k hG hn hN hz
    ⟨(lt_of_not_ge h118).le,hq.2⟩ hrank hmean

#print axioms no_weak_valley
end ForestUnimodality.Stage170Windows.ThroughStrip119
