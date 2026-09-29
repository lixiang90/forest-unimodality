import ForestUnimodality.Stage350JointDirectionTable

/-! The fifteen curvature-assisted directional rows, applied to genuine
forests. The base theorem permits every positive graph order; the order
350 version derives its available-mean threshold from the source density. -/
namespace ForestUnimodality.Stage350JointActualDirection
open Set Stage350JointDirectionTable
variable {V:Type*} [DecidableEq V]

theorem left_coefficient_of_start (i:Fin 15) (hi:reverse i=true)
    {G:SimpleGraph V} {S B:Finset V} {z:ℝ} (k:ℕ)
    (hB:IsMaximumMarginalIndependentOn G S B z) (hG:G.IsAcyclic) (hn:0<S.card)
    (hs:(row i).start≤hardCoreAvailableMean G S B z)
    (hlo:lower i≤z) (hhi:z≤upper i) (hrank:(S.card:ℝ)/4≤hardCoreMean G S z)
    (hmean:hardCoreMean G S z=k) : countIndependent G S (k-1)<countIndependent G S k := by
  have h:=actual_inputs i k hB hG hn hs hlo hhi hrank hmean
  rw [hi] at h
  simp only [Stage350JointInputs.ratio,if_true] at h
  exact JointDirectionCoefficient.left (row_valid i) (envelope_valid i) h (margin_positive i)

theorem right_coefficient_of_start (i:Fin 15) (hi:reverse i=false)
    {G:SimpleGraph V} {S B:Finset V} {z:ℝ} (k:ℕ)
    (hB:IsMaximumMarginalIndependentOn G S B z) (hG:G.IsAcyclic) (hn:0<S.card)
    (hs:(row i).start≤hardCoreAvailableMean G S B z)
    (hlo:lower i≤z) (hhi:z≤upper i) (hrank:(S.card:ℝ)/4≤hardCoreMean G S z)
    (hmean:hardCoreMean G S z=k) : countIndependent G S (k+1)<countIndependent G S k := by
  have h:=actual_inputs i k hB hG hn hs hlo hhi hrank hmean
  rw [hi] at h
  simp only [Stage350JointInputs.ratio,Bool.false_eq_true,if_false] at h
  exact JointDirectionCoefficient.right (row_valid i) (envelope_valid i) h (margin_positive i)

theorem start_le_available (i:Fin 15) {G:SimpleGraph V} {S B:Finset V} {z:ℝ}
    (hB:IsMaximumMarginalIndependentOn G S B z) (hG:G.IsAcyclic) (hn:350≤S.card)
    (hlo:lower i≤z) (hhi:z≤upper i) (hrank:(S.card:ℝ)/4≤hardCoreMean G S z) :
    (row i).start≤hardCoreAvailableMean G S B z := by
  rw [start_match]
  exact Stage350SourceTable.start_le_available (sourceIndex i) hB hG hn hlo hhi hrank

theorem actual_left_coefficient_lt (i:Fin 15) (hi:reverse i=true)
    {G:SimpleGraph V} {S B:Finset V} {z:ℝ} (k:ℕ)
    (hB:IsMaximumMarginalIndependentOn G S B z) (hG:G.IsAcyclic) (hn:350≤S.card)
    (hlo:lower i≤z) (hhi:z≤upper i) (hrank:(S.card:ℝ)/4≤hardCoreMean G S z)
    (hmean:hardCoreMean G S z=k) : countIndependent G S (k-1)<countIndependent G S k :=
  left_coefficient_of_start i hi k hB hG (by omega)
    (start_le_available i hB hG hn hlo hhi hrank) hlo hhi hrank hmean

theorem actual_right_coefficient_lt (i:Fin 15) (hi:reverse i=false)
    {G:SimpleGraph V} {S B:Finset V} {z:ℝ} (k:ℕ)
    (hB:IsMaximumMarginalIndependentOn G S B z) (hG:G.IsAcyclic) (hn:350≤S.card)
    (hlo:lower i≤z) (hhi:z≤upper i) (hrank:(S.card:ℝ)/4≤hardCoreMean G S z)
    (hmean:hardCoreMean G S z=k) : countIndependent G S (k+1)<countIndependent G S k :=
  right_coefficient_of_start i hi k hB hG (by omega)
    (start_le_available i hB hG hn hlo hhi hrank) hlo hhi hrank hmean

theorem left_window_coefficient_lt {G:SimpleGraph V} {S:Finset V} {z:ℝ} (k:ℕ)
    (hG:G.IsAcyclic) (hn:350≤S.card) (hz:z∈Icc (7/10:ℝ) (22/25))
    (hrank:(S.card:ℝ)/4≤hardCoreMean G S z) (hmean:hardCoreMean G S z=k) :
    countIndependent G S (k-1)<countIndependent G S k := by
  obtain ⟨i,hi,hlo,hhi⟩:=covers_left hz.1 hz.2
  obtain ⟨B,hB⟩:=exists_maximumWeightedIndependentOn G S (hardCoreVertexMarginal G S z)
  exact actual_left_coefficient_lt i hi k hB hG hn hlo hhi hrank hmean

theorem right_window_coefficient_lt {G:SimpleGraph V} {S:Finset V} {z:ℝ} (k:ℕ)
    (hG:G.IsAcyclic) (hn:350≤S.card) (hz:z∈Icc (57/50:ℝ) (7/5))
    (hrank:(S.card:ℝ)/4≤hardCoreMean G S z) (hmean:hardCoreMean G S z=k) :
    countIndependent G S (k+1)<countIndependent G S k := by
  obtain ⟨i,hi,hlo,hhi⟩:=covers_right hz.1 hz.2
  obtain ⟨B,hB⟩:=exists_maximumWeightedIndependentOn G S (hardCoreVertexMarginal G S z)
  exact actual_right_coefficient_lt i hi k hB hG hn hlo hhi hrank hmean

#print axioms left_coefficient_of_start
#print axioms right_coefficient_of_start
#print axioms left_window_coefficient_lt
#print axioms right_window_coefficient_lt
end ForestUnimodality.Stage350JointActualDirection
