import ForestUnimodality.CurvatureBudgetGraph
import ForestUnimodality.Stage900SourceTable
import ForestUnimodality.ImprovedSourceTail
import ForestUnimodality.SmoothingInterval

/-! All graph inputs to the central budget follow from the actual verified
source table and finite rational interval conditions. -/
namespace ForestUnimodality.Stage900CurvatureInputs
open Set CurvatureBudget CurvatureBudgetGraph

noncomputable def qLower (p : Parameters) : ℝ := p.a/(1+p.a)
noncomputable def qUpper (p : Parameters) : ℝ := p.b/(1+p.b)
noncomputable def pathLower (p : Parameters) : ℝ := p.a/(33/20+p.a)
noncomputable def pathVariance (p : Parameters) : ℝ :=
  min (pathLower p*(1-pathLower p)) (qUpper p*(1-qUpper p))

structure ScalarValid (i : Fin 28) (p : Parameters) (u : Fin 16→ℝ) : Prop where
  a_match : p.a=((Stage900SourceTable.base i).lower:ℝ)
  b_match : p.b=((Stage900SourceTable.base i).upper:ℝ)
  start_match : p.start=((Stage900SourceTable.row i).start:ℝ)
  D_match : p.D=((Stage900SourceTable.row i).D:ℝ)
  R_match : p.R=((Stage900SourceTable.row i).R:ℝ)
  vmin_left : p.vmin≤qLower p*(1-qLower p)
  vmin_right : p.vmin≤qUpper p*(1-qUpper p)
  vmax_left : qUpper p≤1/2→qUpper p*(1-qUpper p)≤p.vmax
  vmax_right : 1/2≤qLower p→qLower p*(1-qLower p)≤p.vmax
  vmax_center : qLower p<1/2→1/2<qUpper p→1/4≤p.vmax
  eta_left : |1-2*qLower p|≤p.eta
  eta_right : |1-2*qUpper p|≤p.eta
  vmin_near : 9/40≤p.vmin
  tilt_nonneg : ∀j,0≤u j
  tilt_upper : ∀j,u j≤1/2
  tail_rate : ∀j,p.rate j≤qLower p*(1-cut j.val)*u j-
    (((Stage900SourceTable.row i).Cs:ℝ)-cut j.val*pathVariance p)*(u j)^2/2

variable {V : Type*} [DecidableEq V]

theorem actual_inputs (i : Fin 28) (p : Parameters) (u : Fin 16→ℝ)
    (hc : ScalarValid i p u) {G : SimpleGraph V} {S B : Finset V} {z : ℝ} (k : ℕ)
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 900≤S.card) (hz : z∈Icc p.a p.b)
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z)
    (hmean : hardCoreMean G S z=(k:ℝ)) :
    Inputs p G S B z (hardCoreAvailableMean G S B z) k := by
  have ha : 0<p.a := by rw [hc.a_match]; exact_mod_cast (Stage900SourceTable.valid i).lower_pos
  have hz0:=ha.trans_le hz.1
  have hlo : ((Stage900SourceTable.base i).lower:ℝ)≤z := hc.a_match ▸ hz.1
  have hhi : z≤((Stage900SourceTable.base i).upper:ℝ) := hc.b_match ▸ hz.2
  have hb:=Stage900SourceTable.actual_bounds i hB hG hn hlo hhi hrank
  have hs : p.start≤hardCoreAvailableMean G S B z := by
    rw [hc.start_match]
    exact Stage900SourceTable.start_le_available i hB hG hn hlo hhi hrank
  have hq:=SmoothingInterval.activity_fraction_bounds ha.le hz.1 hz.2
  have hvmin : p.vmin≤(z/(1+z))*(1-z/(1+z)) :=
    (le_min hc.vmin_left hc.vmin_right).trans (bernoulli_variance_ge_min hq.1 hq.2)
  refine ⟨hB.subset,hB.independent,hz0,rfl,hs,hmean,?_,?_,hvmin,?_,
    hc.vmin_near.trans hvmin,?_,?_⟩
  · have he:=hardCoreVariance_eq_layer_variance G S B hB.subset hB.independent hz0
    rw [hc.R_match]
    nlinarith only [he,hb.centered_variance]
  · rw [hc.D_match]; exact hb.available_variance
  · exact SmoothingInterval.variance_le_interval_max hq.1 hq.2
      hc.vmax_left hc.vmax_right hc.vmax_center
  · exact SmoothingInterval.asymmetry_le_endpoints hq.1 hq.2 hc.eta_left hc.eta_right
  · intro j
    have hl : pathLower p≤z/(33/20+z) := by
      unfold pathLower
      apply (div_le_div_iff₀ (by positivity : 0<33/20+p.a) (by positivity : 0<33/20+z)).mpr
      nlinarith [hz.1]
    have hcut : cut j.val≤1 := by
      have hj : (j.val:ℝ)<16 := by exact_mod_cast j.isLt
      unfold cut; linarith
    exact hardCoreAvailableLowerTail_le_endpoint_corrected_rate G S B hB.subset hB.independent
      hz0 (hc.tilt_nonneg j) (hc.tilt_upper j) (by norm_num) exp_half_le_33_20 hl hq.2
      (min_le_left _ _) (min_le_right _ _) (cut_pos j.val).le hcut hq.1
      (fun t ht=>hb.tilt_variance t ht.1) (hc.tail_rate j)

#print axioms actual_inputs
end ForestUnimodality.Stage900CurvatureInputs
