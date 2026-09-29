import ForestUnimodality.Stage170FirstWindow
import ForestUnimodality.Stage170SecondWindow
import ForestUnimodality.Stage170Windows.Strip002.Complete
import ForestUnimodality.Stage170Windows.Strip003.Complete
import ForestUnimodality.Stage170Windows.Strip004.Complete

/-! The first five contiguous stage170 activity windows.  Every constituent
window already includes its finite-mean rectangles and the large-mean parent. -/
namespace ForestUnimodality.Stage170Windows.ThroughStrip004
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem no_weak_valley {G : SimpleGraph V} {S : Finset V} {z : ℝ}
    (k : ℕ) (hG : G.IsAcyclic) (hn : 170≤S.card) (hN : S.card≤349) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (1/4:ℝ) (2/7:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  by_cases h₀ : z/(1+z)≤(9/35:ℝ)
  · intro h
    exact (not_lt_of_ge h.1)
      (Stage170FirstWindow.left_window_coefficient_lt k hG hn hN hz ⟨hq.1,h₀⟩ hrank hmean)
  by_cases h₁ : z/(1+z)≤(37/140:ℝ)
  · exact Stage170SecondWindow.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h₀).le,h₁⟩ hrank hmean
  by_cases h₂ : z/(1+z)≤(19/70:ℝ)
  · exact Strip002.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h₁).le,h₂⟩ hrank hmean
  by_cases h₃ : z/(1+z)≤(39/140:ℝ)
  · exact Strip003.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h₂).le,h₃⟩ hrank hmean
  · exact Strip004.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h₃).le,hq.2⟩ hrank hmean

#print axioms no_weak_valley
end ForestUnimodality.Stage170Windows.ThroughStrip004
