import ForestUnimodality.Stage350SourceTable

/-! The frozen source certificates are independent of graph order. This module
reuses their proved scalar validity while replacing the threshold 350 by the
exact positivity/scale hypotheses actually needed by the source argument. -/
namespace ForestUnimodality.Stage350SourceAllOrders
open Stage350SourceTable
variable {V : Type*} [DecidableEq V]

theorem available_variance_any_size (i : Fin 43) {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 0<S.card) (hlo : ((row i).a:ℝ)≤z) (hhi : z≤((row i).b:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreAvailableVariance G S B z≤(row i).D*hardCoreAvailableMean G S B z := by
  have hv := valid i
  have ha : (0:ℝ)<(row i).a := by exact_mod_cast hv.a_pos
  have hz := ha.trans_le hlo
  have hqa : (0:ℝ)<(row i).qa := by exact_mod_cast hv.qa_pos
  have hqlo : ((row i).qa:ℝ)≤z/(1+z) := by
    have he : ((row i).qa:ℝ)=((row i).a:ℝ)/(1+((row i).a:ℝ)) := by exact_mod_cast hv.qa_eq
    rw [he]
    exact Stage900SourceTable.activity_fraction_mono ha hlo
  have hqhi : z/(1+z)≤((row i).qb:ℝ) := by
    have he : ((row i).qb:ℝ)=((row i).b:ℝ)/(1+((row i).b:ℝ)) := by exact_mod_cast hv.qb_eq
    rw [he]
    exact Stage900SourceTable.activity_fraction_mono hz hhi
  have hdensity := density i G hG S hlo hrank
  have hρq := MeanMatchedSourceBudget.density_le_probability_cap G S hz (by omega) hdensity
  have hc := hv.variance_bound
  unfold varianceCheck at hc
  cases hs : varianceSource i with
  | inl j =>
    rw [hs] at hc
    have hP := AffineSource.Parameters.check_sound (affine_checked j)
    apply Stage350SourceBudget.affine_available_variance_le hB hG hz
      (b:=((affineDomain j).b:ℝ))
      (hhi.trans (by exact_mod_cast hc.1)) (by exact_mod_cast hv.rho_pos) hρq hdensity
      (affine j).toReal hP.1 hP.2.1 (affine_valid j) hqa ⟨hqlo,hqhi⟩
    dsimp only at hc
    rcases hc.2 with h | h
    · apply Or.inl
      constructor
      · change (2*((affine j).A:ℝ)/((row i).rho:ℝ)+((affine j).C:ℝ)-1)*((row i).qb:ℝ)≤2*((affine j).A:ℝ)
        exact_mod_cast h.1
      · unfold Stage350SourceBudget.affineCoefficient
        change 1+(2*((affine j).A:ℝ)/((row i).rho:ℝ)+((affine j).C:ℝ)-1)/((row i).qb:ℝ)-
          ((affine j).A:ℝ)/((row i).qb:ℝ)^2≤((row i).D:ℝ)
        exact_mod_cast h.2
    · apply Or.inr
      constructor
      · change 2*((affine j).A:ℝ)≤(2*((affine j).A:ℝ)/((row i).rho:ℝ)+((affine j).C:ℝ)-1)*((row i).qa:ℝ)
        exact_mod_cast h.1
      · unfold Stage350SourceBudget.affineCoefficient
        change 1+(2*((affine j).A:ℝ)/((row i).rho:ℝ)+((affine j).C:ℝ)-1)/((row i).qa:ℝ)-
          ((affine j).A:ℝ)/((row i).qa:ℝ)^2≤((row i).D:ℝ)
        exact_mod_cast h.2
  | inr j =>
    rw [hs] at hc
    exact Stage350SourceBudget.marked_available_variance_le j hB hG
      ((by exact_mod_cast hc.1 : ((Stage350SourceBudget.markedRow j).lower:ℝ)≤(row i).a).trans hlo)
      (hhi.trans (by exact_mod_cast hc.2.1)) hqa hqlo (by exact_mod_cast hc.2.2)

/-- The source bounds do not require order 350. The scale N is any positive
integer no larger than the graph order, and B remains fixed along the tilt. -/
theorem actual_bounds_any_size (i : Fin 43) (N : ℕ) (hN : 0<N) {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : N≤S.card) (hlo : ((row i).a:ℝ)≤z) (hhi : z≤((row i).b:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    MeanMatchedSourceBudget.Bounds G S B z N (row i).rho (row i).qb
      (row i).Cs (row i).D (row i).R := by
  have hv := valid i
  have ha : (0:ℝ)<(row i).a := by exact_mod_cast hv.a_pos
  have hz := ha.trans_le hlo
  have hbasepos : (0:ℝ)<(base i).lower := by
    exact_mod_cast (Stage900SourceTable.valid (selectionIndex i)).lower_pos
  have hbaseLo : ((base i).lower:ℝ)≤z :=
    (show ((base i).lower:ℝ)≤((row i).a:ℝ) by exact_mod_cast hv.selection_lower).trans hlo
  have hbaseHi : z≤((base i).upper:ℝ) := hhi.trans (by exact_mod_cast hv.selection_upper)
  have hqa : ((row i).qa:ℝ)=((row i).a:ℝ)/(1+((row i).a:ℝ)) := by exact_mod_cast hv.qa_eq
  have hqb : ((row i).qb:ℝ)=((row i).b:ℝ)/(1+((row i).b:ℝ)) := by exact_mod_cast hv.qb_eq
  have hqlo : ((row i).qa:ℝ)≤z/(1+z) := by rw [hqa]; exact Stage900SourceTable.activity_fraction_mono ha hlo
  have hqhi : z/(1+z)≤((row i).qb:ℝ) := by rw [hqb]; exact Stage900SourceTable.activity_fraction_mono hz hhi
  have hsourceHi : z≤((nonnegative i).b:ℝ) := hhi.trans (by exact_mod_cast hv.source_upper)
  have hnonneg := NonnegativeSource.Parameters.check_sound (Stage900SourceTable.nonnegative_checked (selectionIndex i))
  have hselect := SelectionSource.Parameters.check_sound (Stage900SourceTable.selection_checked (selectionIndex i))
  have hpre := MeanMatchedSourceBudget.of_certificates hB hG N hN hn
    hbasepos hbaseLo hbaseHi hsourceHi
    (by exact_mod_cast hv.rho_pos) (by exact_mod_cast hv.qa_pos) hqlo hqhi
    (by exact_mod_cast hv.qb_lt_one) (density i G hG S hlo hrank)
    hnonneg.A_nonneg hnonneg.u_nonneg hnonneg.v_nonneg (Stage900SourceTable.nonnegative_valid (selectionIndex i))
    (selection i).toReal hselect.1 hselect.2.1 hselect.2.2 (Stage900SourceTable.selection_valid (selectionIndex i))
    (CW:=((row i).CW:ℝ)) (Cs:=((row i).Cs:ℝ)) (R:=((row i).R:ℝ))
    (D:=((row i).Cs:ℝ)/((row i).qa:ℝ)^2-(1-((row i).qa:ℝ))/((row i).qa:ℝ))
    (by change ((selection i).CJ:ℝ)+2*((selection i).Cmu:ℝ)≤((row i).CW:ℝ); exact_mod_cast hv.CW_bound)
    (by exact_mod_cast hv.Cs_bound) (by exact_mod_cast hv.Cs_cap) le_rfl (by exact_mod_cast hv.R_bound)
  exact ⟨hpre.mean_lower,hpre.mean_pos,hpre.tilt_variance,
    available_variance_any_size i hB hG (lt_of_lt_of_le hN hn) hlo hhi hrank,hpre.centered_variance⟩


#print axioms available_variance_any_size
#print axioms actual_bounds_any_size
end ForestUnimodality.Stage350SourceAllOrders
