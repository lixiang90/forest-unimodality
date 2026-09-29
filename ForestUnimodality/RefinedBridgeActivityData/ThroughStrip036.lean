import ForestUnimodality.RefinedBridgeActivityData.ThroughStrip034
import ForestUnimodality.RefinedBridgeActivityData.Strip035
import ForestUnimodality.RefinedBridgeActivityData.Strip036

/-! Rank and integer mean remain explicit; half-rank follows from the universal mean bound. -/
namespace ForestUnimodality.RefinedBridgeActivityData.ThroughStrip036
variable {V : Type*} [DecidableEq V]

theorem no_weak_valley {G : SimpleGraph V} {S : Finset V} {z : ℝ}
    (k : ℕ) (hG : G.IsAcyclic) (hn : 59≤S.card) (hN : S.card≤349) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (1/4:ℝ) (581/1216:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  by_cases h34 : z/(1+z)≤(1733/3648:ℝ)
  · exact ThroughStrip034.no_weak_valley k hG hn hN hz
      ⟨hq.1,h34⟩ hrank hmean
  have hupper := hardCoreMean_le_card_mul_activity G S hz.le
  rw [hmean,mul_div_assoc] at hupper
  have hn0 : (0:ℝ)≤S.card := by positivity
  have hmul := mul_le_mul_of_nonneg_left hq.2 hn0
  have hhalfR : 2*(k:ℝ)≤S.card := by nlinarith
  have hhalf : 2*k≤S.card := by exact_mod_cast hhalfR
  by_cases h35 : z/(1+z)≤(869/1824:ℝ)
  · exact Strip035.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h34).le,h35⟩ hrank hmean hhalf
  exact Strip036.no_weak_valley k hG hn hN hz
    ⟨(lt_of_not_ge h35).le,hq.2⟩ hrank hmean hhalf

#print axioms no_weak_valley
end ForestUnimodality.RefinedBridgeActivityData.ThroughStrip036
