import ForestUnimodality.Stage350PlainDirectionInputs
import ForestUnimodality.Stage350SourceAllOrders
import ForestUnimodality.Stage350AffineTailAllOrders

/-! Large available mean suffices for the old direction budget even when
the forest has fewer than 350 vertices. All statistical inputs remain actual. -/
namespace ForestUnimodality.Stage350PlainDirectionAllOrders
open Set DirectionBudget ReciprocalGradientBudget Stage900DirectionInputs
open Stage350PlainDirectionInputs

variable {V : Type*} [DecidableEq V]

theorem actual_inputs_of_start (i : Fin 43) (p : Parameters) (hp : p.Valid)
    (g0 g1 : GradientProfile) (j0 j1 : Fin 15) (u0 u1 : ℝ)
    (hc : ScalarValid i p g0 g1 j0 j1 u0 u1)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ} (k : ℕ)
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 0 < S.card) (hs : p.start ≤ hardCoreAvailableMean G S B z)
    (hz : z ∈ Icc p.a p.b)
    (hrank : (S.card : ℝ)/4 ≤ hardCoreMean G S z)
    (hmean : hardCoreMean G S z = (k : ℝ)) :
    DirectionBudgetGraph.Inputs p G S B z (hardCoreAvailableMean G S B z) k g0 g1 := by
  have ha : 0 < p.a := by
    rw [hc.a_match]
    exact_mod_cast (Stage350SourceTable.valid i).a_pos
  have hz0 := ha.trans_le hz.1
  have hlo : ((Stage350SourceTable.row i).a : ℝ) ≤ z := hc.a_match ▸ hz.1
  have hhi : z ≤ ((Stage350SourceTable.row i).b : ℝ) := hc.b_match ▸ hz.2
  have hb := Stage350SourceAllOrders.actual_bounds_any_size i 1 (by norm_num)
    hB hG (by omega) hlo hhi hrank
  have hq := SmoothingInterval.activity_fraction_bounds ha.le hz.1 hz.2
  have hvmin : p.vmin ≤ (z/(1+z))*(1-z/(1+z)) :=
    (le_min hc.vmin_left hc.vmin_right).trans (bernoulli_variance_ge_min hq.1 hq.2)
  have hvmax : (z/(1+z))*(1-z/(1+z)) ≤ p.vmax :=
    SmoothingInterval.variance_le_interval_max hq.1 hq.2
      hc.vmax_left hc.vmax_right hc.vmax_center
  refine ⟨hB.subset, hB.independent, hz0, hz, rfl, hs, hmean, ?_, ?_, ?_, ?_,
    hvmin, hvmax, ?_, ?_, ?_, ?_, hc.constant0, hc.constant1⟩
  · have he := hardCoreVariance_eq_layer_variance G S B hB.subset hB.independent hz0
    rw [hc.R_match]
    nlinarith only [he, hb.centered_variance]
  · rw [hc.D_match]
    exact hb.available_variance
  · exact Stage350AffineTailAllOrders.actual_affine_tail_le_rate i j0 hB hG hn hlo hhi hrank
      hc.cap0 hp.alpha_pos.le hc.u0_nonneg hc.rate0
  · exact Stage350AffineTailAllOrders.actual_affine_tail_le_rate i j1 hB hG hn hlo hhi hrank
      hc.cap1 hp.alpha1_pos.le hc.u1_nonneg hc.rate1
  · exact SmoothingInterval.asymmetry_le_endpoints hq.1 hq.2 hc.eta_left hc.eta_right
  · exact SmoothingInterval.cutoff_of_variance_lower hc.vmin_sixth hvmin
      hp.T_pos hp.T_lt_pi hc.cutoff_damping hc.cutoff_quartic
  · exact profile_valid_of_range hc.profile0 hp.vmin_pos hvmin (mul_pos hp.alpha_pos hp.start_pos)
      (mul_le_mul_of_nonneg_left hs hp.alpha_pos.le) hq.1 hq.2
  · exact profile_valid_of_range hc.profile1 hp.vmin_pos hvmin (mul_pos hp.alpha1_pos hp.start_pos)
      (mul_le_mul_of_nonneg_left hs hp.alpha1_pos.le) hq.1 hq.2

#print axioms actual_inputs_of_start
end ForestUnimodality.Stage350PlainDirectionAllOrders
