import ForestUnimodality.Stage350CurvatureInputs
import ForestUnimodality.Stage350SourceAllOrders
import ForestUnimodality.Stage350AffineTailAllOrders

/-! The central kernel is independent of graph order. Only the actual layer
mean must exceed the numerical row's starting scale. -/
namespace ForestUnimodality.Stage350VerifiedTail
variable {V : Type*} [DecidableEq V]

theorem Verified.actual_any_size {i : Fin 43} {alpha rate : ℝ} (w : Verified i alpha rate)
    {G : SimpleGraph V} {S I : Finset V} {z : ℝ}
    (hI : IsMaximumMarginalIndependentOn G S I z) (hG : G.IsAcyclic)
    (hn : 0<S.card) (hlo : ((Stage350SourceTable.row i).a:ℝ)≤z)
    (hhi : z≤((Stage350SourceTable.row i).b:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreAvailableLowerTail G S I z (alpha*hardCoreAvailableMean G S I z)≤
      Real.exp (-rate*hardCoreAvailableMean G S I z) :=
  Stage350AffineTailAllOrders.actual_affine_tail_le_rate i w.source hI hG hn hlo hhi hrank
    w.cap w.alpha_nonneg w.tilt_nonneg w.rate_lower
end ForestUnimodality.Stage350VerifiedTail

namespace ForestUnimodality.Stage350CurvatureInputs
open Set Stage350CurvatureBudget Stage350VerifiedTail
variable {V : Type*} [DecidableEq V]

theorem actual_inputs_any_size (i : Fin 43) (p : Parameters)
    (hc : ScalarValid i p)
    (gap : ∀j : Fin 40, Verified i (profileCut p.largeBeta (j.val+1)) (p.gapRate j))
    (bad : ∀j : Fin 24, Verified i (cut j.val) (p.badRate j))
    {G : SimpleGraph V} {S I : Finset V} {z : ℝ} (k : ℕ)
    (hI : IsMaximumMarginalIndependentOn G S I z) (hG : G.IsAcyclic)
    (hn : 0<S.card) (hz : z∈Icc p.a p.b)
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z)
    (hmean : hardCoreMean G S z=(k:ℝ))
    (hs : p.start≤hardCoreAvailableMean G S I z) :
    Stage350CurvatureGraph.Inputs p G S I z (hardCoreAvailableMean G S I z) k := by
  have ha : 0<p.a := by
    rw [hc.a_match]
    exact_mod_cast (Stage350SourceTable.valid i).a_pos
  have hz0:=ha.trans_le hz.1
  have hlo : ((Stage350SourceTable.row i).a:ℝ)≤z := hc.a_match ▸ hz.1
  have hhi : z≤((Stage350SourceTable.row i).b:ℝ) := hc.b_match ▸ hz.2
  have hb:=Stage350SourceAllOrders.actual_bounds_any_size i 1 (by norm_num)
    hI hG (by omega) hlo hhi hrank
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
    exact (gap j).actual_any_size hI hG hn hlo hhi hrank
  · intro j
    exact (bad j).actual_any_size hI hG hn hlo hhi hrank

#print axioms actual_inputs_any_size
end ForestUnimodality.Stage350CurvatureInputs
