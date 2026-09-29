import ForestUnimodality.Stage350SourceTable
import ForestUnimodality.AffineSourceLibrary

namespace ForestUnimodality.Stage350SourceTable
open Set

noncomputable def affineTailRate (i : Fin 43) (j : Fin 15) (α u : ℝ) : ℝ :=
  min (AffineLaplace.tailRate (AffineSourceLibrary.parameters j).A
    (AffineSourceLibrary.parameters j).C (row i).rho α u (row i).qa)
    (AffineLaplace.tailRate (AffineSourceLibrary.parameters j).A
      (AffineSourceLibrary.parameters j).C (row i).rho α u (row i).qb)

variable {V : Type*} [DecidableEq V]

/-- The complete affine rate applies at every actual activity in the row,
with no retained statistical hypothesis or reoptimization of B along t. -/
theorem actual_affine_tail (i : Fin 43) (j : Fin 15)
    {G : SimpleGraph V} {S B : Finset V} {z α u : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 350≤S.card) (hlo : ((row i).a:ℝ)≤z) (hhi : z≤((row i).b:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z)
    (hcap : (row i).b≤(AffineSourceLibrary.domain j).b)
    (hα : 0≤α) (hu : 0≤u) :
    hardCoreAvailableLowerTail G S B z (α*hardCoreAvailableMean G S B z) ≤
      Real.exp (-affineTailRate i j α u*hardCoreAvailableMean G S B z) := by
  have hv := valid i
  have ha : (0:ℝ)<(row i).a := by exact_mod_cast hv.a_pos
  have hz := ha.trans_le hlo
  have hdensity := density i G hG S hlo hrank
  have hρq := MeanMatchedSourceBudget.density_le_probability_cap G S hz (by omega) hdensity
  have hqa : ((row i).qa:ℝ)=((row i).a:ℝ)/(1+((row i).a:ℝ)) := by exact_mod_cast hv.qa_eq
  have hqb : ((row i).qb:ℝ)=((row i).b:ℝ)/(1+((row i).b:ℝ)) := by exact_mod_cast hv.qb_eq
  have hqlo : ((row i).qa:ℝ)≤z/(1+z) := by rw [hqa]; exact Stage900SourceTable.activity_fraction_mono ha hlo
  have hqhi : z/(1+z)≤((row i).qb:ℝ) := by rw [hqb]; exact Stage900SourceTable.activity_fraction_mono hz hhi
  exact AffineSourceLibrary.actual_tail_of_endpoints j hB hG hz
    (hhi.trans (by exact_mod_cast hcap)) (by exact_mod_cast hv.rho_pos) hρq hu hα hdensity
    (by exact_mod_cast hv.qa_pos.le) (by exact_mod_cast hv.qb_lt_one.le) ⟨hqlo,hqhi⟩
    (min_le_left _ _) (min_le_right _ _)

theorem actual_affine_tail_le_rate (i : Fin 43) (j : Fin 15)
    {G : SimpleGraph V} {S B : Finset V} {z α u rate : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 350≤S.card) (hlo : ((row i).a:ℝ)≤z) (hhi : z≤((row i).b:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z)
    (hcap : (row i).b≤(AffineSourceLibrary.domain j).b)
    (hα : 0≤α) (hu : 0≤u) (hrate : rate≤affineTailRate i j α u) :
    hardCoreAvailableLowerTail G S B z (α*hardCoreAvailableMean G S B z) ≤
      Real.exp (-rate*hardCoreAvailableMean G S B z) := by
  apply (actual_affine_tail i j hB hG hn hlo hhi hrank hcap hα hu).trans
  apply Real.exp_le_exp.mpr
  have hm := (actual_bounds i hB hG hn hlo hhi hrank).mean_pos.le
  nlinarith [mul_le_mul_of_nonneg_right hrate hm]

#print axioms actual_affine_tail
#print axioms actual_affine_tail_le_rate
end ForestUnimodality.Stage350SourceTable
