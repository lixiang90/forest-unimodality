import ForestUnimodality.Stage350CurvatureGraph
import ForestUnimodality.Stage350VerifiedTail
import ForestUnimodality.Stage900DirectionInputs

/-! The statistical and tail premises of the central budget, discharged for
the actual hard-core layer law by verified stage-350 source rows. -/
namespace ForestUnimodality.Stage350CurvatureInputs
open Set Stage350CurvatureBudget Stage350VerifiedTail

noncomputable def qLower (p : Parameters) : ℝ := p.a/(1+p.a)
noncomputable def qUpper (p : Parameters) : ℝ := p.b/(1+p.b)

structure ScalarValid (i : Fin 43) (p : Parameters) : Prop where
  a_match : p.a = ((Stage350SourceTable.row i).a : ℝ)
  b_match : p.b = ((Stage350SourceTable.row i).b : ℝ)
  start_match : p.start = ((Stage350SourceTable.row i).start : ℝ)
  D_match : p.D = ((Stage350SourceTable.row i).D : ℝ)
  R_match : p.R = ((Stage350SourceTable.row i).R : ℝ)
  vmin_left : p.vmin ≤ qLower p * (1-qLower p)
  vmin_right : p.vmin ≤ qUpper p * (1-qUpper p)
  vmax_left : qUpper p ≤ 1/2 → qUpper p * (1-qUpper p) ≤ p.vmax
  vmax_right : 1/2 ≤ qLower p → qLower p * (1-qLower p) ≤ p.vmax
  vmax_center : qLower p < 1/2 → 1/2 < qUpper p → 1/4 ≤ p.vmax
  eta_left : |1-2*qLower p| ≤ p.eta
  eta_right : |1-2*qUpper p| ≤ p.eta
  vmin_near : 9/40 ≤ p.vmin

variable {V : Type*} [DecidableEq V]

theorem actual_inputs (i : Fin 43) (p : Parameters)
    (hc : ScalarValid i p)
    (gap : ∀j : Fin 40, Verified i (profileCut p.largeBeta (j.val+1)) (p.gapRate j))
    (bad : ∀j : Fin 24, Verified i (cut j.val) (p.badRate j))
    {G : SimpleGraph V} {S I : Finset V} {z : ℝ} (k : ℕ)
    (hI : IsMaximumMarginalIndependentOn G S I z) (hG : G.IsAcyclic)
    (hn : 350≤S.card) (hz : z∈Icc p.a p.b)
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z)
    (hmean : hardCoreMean G S z=(k:ℝ)) :
    Stage350CurvatureGraph.Inputs p G S I z (hardCoreAvailableMean G S I z) k := by
  have ha : 0<p.a := by
    rw [hc.a_match]
    exact_mod_cast (Stage350SourceTable.valid i).a_pos
  have hz0:=ha.trans_le hz.1
  have hlo : ((Stage350SourceTable.row i).a:ℝ)≤z := hc.a_match ▸ hz.1
  have hhi : z≤((Stage350SourceTable.row i).b:ℝ) := hc.b_match ▸ hz.2
  have hb:=Stage350SourceTable.actual_bounds i hI hG hn hlo hhi hrank
  have hs : p.start≤hardCoreAvailableMean G S I z := by
    rw [hc.start_match]
    exact Stage350SourceTable.start_le_available i hI hG hn hlo hhi hrank
  have hq:=SmoothingInterval.activity_fraction_bounds ha.le hz.1 hz.2
  have hvmin : p.vmin≤(z/(1+z))*(1-z/(1+z)) :=
    (le_min hc.vmin_left hc.vmin_right).trans (bernoulli_variance_ge_min hq.1 hq.2)
  have hvmax : (z/(1+z))*(1-z/(1+z))≤p.vmax :=
    SmoothingInterval.variance_le_interval_max hq.1 hq.2
      hc.vmax_left hc.vmax_right hc.vmax_center
  refine ⟨hI.subset,hI.independent,hz0,rfl,hs,hmean,?_,?_,hvmin,hvmax,
    hc.vmin_near.trans hvmin,?_,?_,?_⟩
  · have he:=hardCoreVariance_eq_layer_variance G S I hI.subset hI.independent hz0
    rw [hc.R_match]
    nlinarith only [he,hb.centered_variance]
  · rw [hc.D_match]
    exact hb.available_variance
  · exact SmoothingInterval.asymmetry_le_endpoints hq.1 hq.2 hc.eta_left hc.eta_right
  · intro j
    exact (gap j).actual hI hG hn hlo hhi hrank
  · intro j
    exact (bad j).actual hI hG hn hlo hhi hrank

#print axioms actual_inputs
end ForestUnimodality.Stage350CurvatureInputs
