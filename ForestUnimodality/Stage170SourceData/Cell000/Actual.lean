import ForestUnimodality.Stage350SourceAllOrders
import ForestUnimodality.Stage170SourceData.Cell000.Rate

namespace ForestUnimodality.Stage170SourceData.Cell000
open Stage170KernelData.Cell000
variable {V : Type*} [DecidableEq V]

private theorem activity_bounds {z : ℝ} (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (1/4:ℝ) (9/35:ℝ)) :
    (1/3:ℝ)≤z ∧ z≤2/5 ∧ z≤1/2 := by
  have hlo := (le_div_iff₀ (by positivity : 0<1+z)).mp hq.1
  have hhi := (div_le_iff₀ (by positivity : 0<1+z)).mp hq.2
  constructor
  · linarith
  constructor <;> linarith

theorem available_mean_lower {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hq : z/(1+z)∈Set.Icc (1/4:ℝ) (9/35:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (N : ℕ) (hn : N≤S.card) :
    (1/4:ℝ)*N/(2*(9/35))≤hardCoreAvailableMean G S B z := by
  exact MeanMatchedSourceBudget.available_mean_lower hB hG hz (by norm_num) hq.2 N hn
    (by linarith)

theorem available_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (1/4:ℝ) (9/35:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreAvailableVariance G S B z≤(D:ℝ)*hardCoreAvailableMean G S B z := by
  have hdensity : (1/4:ℝ)*(S.card:ℝ)≤hardCoreMean G S z := by linarith
  have hP := AffineSource.Parameters.check_sound AffineSourceData.Case01.parameters_checked
  apply Stage350SourceBudget.affine_available_variance_le hB hG hz
    (b:=(1/2:ℝ)) (activity_bounds hz hq).2.2 (by norm_num)
    (MeanMatchedSourceBudget.density_le_probability_cap G S hz hS hdensity) hdensity
    AffineSourceData.Case01.parameters.toReal hP.1 hP.2.1
    (by simpa [AffineSourceData.Case01.domain] using AffineSourceData.Case01.source_valid)
    (by norm_num : (0:ℝ)<1/4) hq
  left
  norm_num [AffineSourceData.Case01.parameters,AffineSource.Parameters.toReal,
    Stage350SourceBudget.affineCoefficient,D]

theorem centered_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hq : z/(1+z)∈Set.Icc (1/4:ℝ) (9/35:ℝ)) :
    hardCoreLayerMeanVariance G S B z≤
      (R:ℝ)*(z/(1+z)*(1-z/(1+z)))*hardCoreAvailableMean G S B z := by
  have hab := activity_bounds hz hq
  have hv := Stage350SourceTable.valid 0
  have hs := SelectionSource.Parameters.check_sound (Stage900SourceTable.selection_checked (Stage350SourceTable.selectionIndex 0))
  have hlo : ((Stage350SourceTable.base 0).lower:ℝ)≤z := by
    apply le_trans _ hab.1
    have hh : (Stage350SourceTable.base 0).lower≤(1/3:ℚ) := by
      simpa [Stage350SourceTable.row] using hv.selection_lower
    have hc := (Rat.cast_le (K:=ℝ)).mpr hh
    norm_num at hc ⊢
    exact hc
  have hhi : z≤((Stage350SourceTable.base 0).upper:ℝ) := by
    apply le_trans hab.2.1
    have hh : (2/5:ℚ)≤(Stage350SourceTable.base 0).upper := by
      simpa [Stage350SourceTable.row] using hv.selection_upper
    have hc := (Rat.cast_le (K:=ℝ)).mpr hh
    norm_num at hc ⊢
    exact hc
  have hselect := hB.variance_le_mass_of_selection_certificate hG
    (show (0:ℝ)<(Stage350SourceTable.base 0).lower by
      exact_mod_cast (Stage900SourceTable.valid 0).lower_pos)
    hlo hhi (Stage350SourceTable.selection 0).toReal hs.1 hs.2.1 hs.2.2
    (Stage900SourceTable.selection_valid (Stage350SourceTable.selectionIndex 0))
  have hc : ((Stage350SourceTable.selection 0).CJ:ℝ)+
      2*((Stage350SourceTable.selection 0).Cmu:ℝ)≤(2101229/1250000:ℝ) := by
    have hh : (Stage350SourceTable.selection 0).CJ+
        2*(Stage350SourceTable.selection 0).Cmu≤(2101229/1250000:ℚ) := by
      simpa [Stage350SourceTable.row] using hv.CW_bound
    have hc := (Rat.cast_le (K:=ℝ)).mpr hh
    norm_num at hc ⊢
    exact hc
  have hmass : 0≤hardCoreOccupiedMass G S B z := by
    rw [hardCoreOccupiedMass_eq_activity_available_mean G S B hB.subset hB.independent hz]
    exact mul_nonneg (by positivity) (hardCoreAvailableMean_nonneg G S B hz.le)
  apply MeanMatchedSourceBudget.centered_variance_bound hB.subset hB.independent hz hq.2
    (by norm_num : (9/35:ℝ)<1) (by norm_num : (0:ℝ)≤2101229/1250000)
    (by norm_num [R])
  exact hselect.trans (mul_le_mul_of_nonneg_right hc hmass)

theorem total_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hq : z/(1+z)∈Set.Icc (1/4:ℝ) (9/35:ℝ)) :
    hardCoreVariance G S z≤
      (z/(1+z)*(1-z/(1+z))+(R*vmax:ℚ))*hardCoreAvailableMean G S B z+0 := by
  have hc := centered_variance hB hG hz hq
  have hv : z/(1+z)*(1-z/(1+z))≤(vmax:ℝ) := by
    have hh := mul_nonneg (sub_nonneg.mpr hq.2)
      (show 0≤1-(9/35:ℝ)-z/(1+z) by linarith [hq.2])
    norm_num [vmax] at *
    nlinarith
  have hm := hardCoreAvailableMean_nonneg G S B hz.le
  have hR : (0:ℝ)≤R := by norm_num [R]
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hR) hm
  have he := hardCoreVariance_eq_layer_variance G S B hB.subset hB.independent hz
  push_cast
  nlinarith

theorem laplace_bound {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (1/4:ℝ) (9/35:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    ∀i∈row.terms,hardCoreLayerLaplace G S B z (row.retention i)≤
      Real.exp (-(rate i:ℝ)*hardCoreAvailableMean G S B z) := by
  intro i _
  fin_cases i
  norm_num [row]
  have hh := AffineSourceLaplaceRate.actual_laplace_of_certificates 0 lowerWitness upperWitness
    (ρ:=(1/4:ℚ)) (u:=tilt) (qa:=(1/4:ℚ)) (qb:=(9/35:ℚ))
    (retention:=(1/2:ℚ)) (rate:=rate 0)
    (by simpa [AffineSourceLibrary.parameters,AffineSourceData.Case01.parameters] using lower_checked)
    (by simpa [AffineSourceLibrary.parameters,AffineSourceData.Case01.parameters] using upper_checked)
    (by norm_num : (0:ℚ)≤1/2) retention_checked (by norm_num : (0:ℚ)≤1/4)
    (by norm_num : (9/35:ℚ)≤1) hB hG hz
    (by simpa [AffineSourceLibrary.domain,AffineSourceData.Case01.domain] using (activity_bounds hz hq).2.2)
    hS (by norm_num; exact hq) (by norm_num; linarith)
  simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,neg_mul] using hh

theorem actual_inputs {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    (hardCoreVariance G S z≤
      (z/(1+z)*(1-z/(1+z))+(R*vmax:ℚ))*hardCoreAvailableMean G S B z+0) ∧
    (hardCoreAvailableVariance G S B z≤(D:ℝ)*hardCoreAvailableMean G S B z) ∧
    (∀i∈row.terms,hardCoreLayerLaplace G S B z (row.retention i)≤
      Real.exp (-(rate i:ℝ)*hardCoreAvailableMean G S B z)) := by
  have hq' : z/(1+z)∈Set.Icc (1/4:ℝ) (9/35:ℝ) := by
    simpa [interval] using hq
  exact ⟨total_variance hB hG hz hq',available_variance hB hG hz hS hq' hrank,
    laplace_bound hB hG hz hS hq' hrank⟩

#print axioms available_mean_lower
#print axioms available_variance
#print axioms centered_variance
#print axioms total_variance
#print axioms laplace_bound
#print axioms actual_inputs
end ForestUnimodality.Stage170SourceData.Cell000
