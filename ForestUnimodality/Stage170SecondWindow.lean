import ForestUnimodality.Stage170KernelData.Cell429.Conclusion
import ForestUnimodality.Stage170KernelData.Cell350.Conclusion
import ForestUnimodality.Stage170KernelData.Cell004.Conclusion
import ForestUnimodality.Stage170KernelData.Cell005.Conclusion
import ForestUnimodality.Stage170KernelData.Cell006.Conclusion
import ForestUnimodality.Stage170KernelData.Cell007.Conclusion
import ForestUnimodality.Stage170SecondWindowGeometry

/-! The whole second activity interval, with no hypothesis on the available mean.
The finite rectangles cover the lower part; the checked analytic row covers the rest. -/
namespace ForestUnimodality.Stage170SecondWindow
open Stage170Geometry
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem actual_left_coefficient_lt {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z)
    (hG : G.IsAcyclic) (hn : 170 ≤ S.card) (hN : S.card ≤ 349)
    (hz : 0 < z) (hk : 1 ≤ k)
    (hq : z / (1 + z) ∈ Set.Icc (9/35 : ℝ) (37/140 : ℝ))
    (hrank : (S.card : ℝ) / 4 ≤ hardCoreMean G S z)
    (hmean : hardCoreMean G S z = k) :
    countIndependent G S (k-1) < countIndependent G S k := by
  rcases actual_finite_cover_or_left_growth k hB hG hn hz hk hq hrank hmean with hfinite | hgrowth
  · obtain ⟨i, hi, hpoint⟩ := hfinite
    have hS : 0 < S.card := by omega
    have hcases : i=429 ∨ i=350 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using hi
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Stage170KernelData.Cell429.actual_left_coefficient_lt k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell350.actual_left_coefficient_lt k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell004.actual_left_coefficient_lt k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell005.actual_left_coefficient_lt k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell006.actual_left_coefficient_lt k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell007.actual_left_coefficient_lt k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact hgrowth

/-- The maximizing marginal independent set is chosen internally. -/
theorem left_window_coefficient_lt {G : SimpleGraph V} {S : Finset V} {z : ℝ}
    (k : ℕ) (hG : G.IsAcyclic) (hn : 170 ≤ S.card) (hN : S.card ≤ 349)
    (hz : 0 < z)
    (hq : z/(1+z)∈Set.Icc (9/35:ℝ) (37/140:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z)
    (hmean : hardCoreMean G S z=k) :
    countIndependent G S (k-1)<countIndependent G S k := by
  obtain ⟨B,hB⟩ := exists_maximumWeightedIndependentOn G S (hardCoreVertexMarginal G S z)
  have hnR : (170:ℝ)≤S.card := by exact_mod_cast hn
  have hkR : (1:ℝ)≤(k:ℝ) := by linarith
  have hk : 1≤k := by exact_mod_cast hkR
  exact actual_left_coefficient_lt k hB hG hn hN hz hk hq hrank hmean

theorem no_weak_valley {G : SimpleGraph V} {S : Finset V} {z : ℝ}
    (k : ℕ) (hG : G.IsAcyclic) (hn : 170 ≤ S.card) (hN : S.card ≤ 349)
    (hz : 0 < z) (hq : z/(1+z)∈Set.Icc (9/35:ℝ) (37/140:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  intro h
  exact (not_lt_of_ge h.1) (left_window_coefficient_lt k hG hn hN hz hq hrank hmean)

#print axioms no_weak_valley
#print axioms actual_left_coefficient_lt
#print axioms left_window_coefficient_lt
end ForestUnimodality.Stage170SecondWindow
