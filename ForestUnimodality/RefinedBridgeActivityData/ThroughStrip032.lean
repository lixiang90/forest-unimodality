import ForestUnimodality.BridgeActivityData.ThroughStrip031
import ForestUnimodality.RefinedBridgeActivityData.Strip032

/-! Consecutive activity coverage through strip32. The universal mean upper
bound discharges the refined interface's half-rank premise in this activity
range. Rank and integer mean remain explicit. Not all-order unimodality. -/
namespace ForestUnimodality.RefinedBridgeActivityData.ThroughStrip032
variable {V : Type*} [DecidableEq V]

theorem no_weak_valley {G : SimpleGraph V} {S : Finset V} {z : ℝ}
    (k : ℕ) (hG : G.IsAcyclic) (hn : 59≤S.card) (hN : S.card≤349) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (1/4:ℝ) (1687/3572:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  by_cases h : z/(1+z)≤(841/1786:ℝ)
  · exact BridgeActivityData.ThroughStrip031.no_weak_valley k hG hn hN hz
      ⟨hq.1,h⟩ hrank hmean
  · have hupper := hardCoreMean_le_card_mul_activity G S hz.le
    rw [hmean,mul_div_assoc] at hupper
    have hn0 : (0:ℝ)≤S.card := by positivity
    have hmul := mul_le_mul_of_nonneg_left hq.2 hn0
    have hhalfR : 2*(k:ℝ)≤S.card := by nlinarith
    have hhalf : 2*k≤S.card := by exact_mod_cast hhalfR
    exact Strip032.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h).le,hq.2⟩ hrank hmean hhalf

#print axioms no_weak_valley
end ForestUnimodality.RefinedBridgeActivityData.ThroughStrip032
