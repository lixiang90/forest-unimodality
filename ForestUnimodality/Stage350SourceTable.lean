import ForestUnimodality.Stage350SourceRows

namespace ForestUnimodality.Stage350SourceTable
variable {V : Type*} [DecidableEq V]

/-- The density belongs to this row's actual activity, including narrower
subintervals of an inherited selection certificate. -/
theorem density (i : Fin 43) (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V)
    {z : ℝ} (hlo : ((row i).a:ℝ)≤z)
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    (row i).rho*(S.card:ℝ)≤hardCoreMean G S z := by
  have hv := valid i
  have ha : (0:ℝ)<(row i).a := by exact_mod_cast hv.a_pos
  have hrho : (0:ℝ)≤(row i).rho := by exact_mod_cast hv.rho_pos.le
  by_cases hh : (1:ℚ)≤(row i).a
  · apply forest_density_of_upper_activity_certificate G hG S
      (by exact_mod_cast hh) hlo hrho
    have hcert := hv.density
    rw [if_pos hh] at hcert
    have hr := (Rat.cast_le (K:=ℝ)).mpr hcert
    norm_num at hr ⊢
    exact hr
  · have hA : (43/100:ℝ)≤(max (nonnegative i).A (43/100:ℚ):ℝ) := by
      have hr := (Rat.cast_le (K:=ℝ)).mpr (le_max_right (nonnegative i).A (43/100:ℚ))
      norm_num at hr ⊢
    apply forest_central_density_of_lower_activity_certificate G hG S
      (A:=(max (nonnegative i).A (43/100:ℚ):ℝ)) ha
      (by exact_mod_cast le_of_not_ge hh) hlo hA hrank
    have hcert := hv.density
    rw [if_neg hh] at hcert
    have hr := (Rat.cast_le (K:=ℝ)).mpr hcert
    norm_num at hr ⊢
    exact hr

theorem available_variance (i : Fin 43) {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 350≤S.card) (hlo : ((row i).a:ℝ)≤z) (hhi : z≤((row i).b:ℝ))
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

/-- Complete actual source interface for each of the forty-three frozen rows.
Only original graph, size, activity and necessary central-rank hypotheses
remain. The fixed B is never optimized again along the tilt path. -/
theorem actual_bounds (i : Fin 43) {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 350≤S.card) (hlo : ((row i).a:ℝ)≤z) (hhi : z≤((row i).b:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    MeanMatchedSourceBudget.Bounds G S B z 350 (row i).rho (row i).qb
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
  have hpre := MeanMatchedSourceBudget.of_certificates hB hG 350 (by decide) hn
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
    available_variance i hB hG hn hlo hhi hrank,hpre.centered_variance⟩

theorem start_le_available (i : Fin 43) {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 350≤S.card) (hlo : ((row i).a:ℝ)≤z) (hhi : z≤((row i).b:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    ((row i).start:ℝ)≤hardCoreAvailableMean G S B z := by
  have hs : ((row i).start:ℝ)≤((row i).rho:ℝ)*350/(2*((row i).qb:ℝ)) := by
    exact_mod_cast (valid i).start_bound
  exact hs.trans (actual_bounds i hB hG hn hlo hhi hrank).mean_lower

#print axioms density
#print axioms available_variance
#print axioms actual_bounds
#print axioms start_le_available
end ForestUnimodality.Stage350SourceTable
