import ForestUnimodality.Stage350AffineTail
import ForestUnimodality.AffineTailRateCertificate
import ForestUnimodality.Stage900DirectionInputs

/-! Actual stage-350 plain direction inputs. The affine source hypotheses are
discharged by their continuous certificates, including every downward tilt.
The independent marked source is used only for the original-activity variance. -/
namespace ForestUnimodality.Stage350PlainDirectionInputs
open Set DirectionBudget ReciprocalGradientBudget Stage900DirectionInputs

structure ScalarValid (i : Fin 43) (p : Parameters) (g0 g1 : GradientProfile)
    (j0 j1 : Fin 15) (u0 u1 : ℝ) : Prop where
  a_match : p.a = ((Stage350SourceTable.row i).a : ℝ)
  b_match : p.b = ((Stage350SourceTable.row i).b : ℝ)
  start_match : p.start = ((Stage350SourceTable.row i).start : ℝ)
  D_match : p.D = ((Stage350SourceTable.row i).D : ℝ)
  R_match : p.R = ((Stage350SourceTable.row i).R : ℝ)
  vmin_left : p.vmin ≤ qLower p * (1 - qLower p)
  vmin_right : p.vmin ≤ qUpper p * (1 - qUpper p)
  vmax_left : qUpper p ≤ 1/2 → qUpper p * (1 - qUpper p) ≤ p.vmax
  vmax_right : 1/2 ≤ qLower p → qLower p * (1 - qLower p) ≤ p.vmax
  vmax_center : qLower p < 1/2 → 1/2 < qUpper p → 1/4 ≤ p.vmax
  eta_left : |1 - 2*qLower p| ≤ p.eta
  eta_right : |1 - 2*qUpper p| ≤ p.eta
  vmin_sixth : 1/6 ≤ p.vmin
  cutoff_damping : 1/6 ≤ p.vmin * (1-p.T^2/12)
  cutoff_quartic : 1-5*p.vmin-10*p.vmin^2+(15/512)*p.T^2 ≤ 0
  profile0 : ProfileRange g0 (qLower p) (qUpper p) p.vmin (p.alpha*p.start)
  profile1 : ProfileRange g1 (qLower p) (qUpper p) p.vmin (p.alpha1*p.start)
  constant0 : g0.constant ≤ p.c0
  constant1 : g1.constant ≤ p.c1
  cap0 : (Stage350SourceTable.row i).b ≤ (AffineSourceLibrary.domain j0).b
  cap1 : (Stage350SourceTable.row i).b ≤ (AffineSourceLibrary.domain j1).b
  u0_nonneg : 0 ≤ u0
  u1_nonneg : 0 ≤ u1
  rate0 : p.rate0 ≤ Stage350SourceTable.affineTailRate i j0 p.alpha u0
  rate1 : p.rate1 ≤ Stage350SourceTable.affineTailRate i j1 p.alpha1 u1

variable {V : Type*} [DecidableEq V]

theorem actual_inputs (i : Fin 43) (p : Parameters) (hp : p.Valid)
    (g0 g1 : GradientProfile) (j0 j1 : Fin 15) (u0 u1 : ℝ)
    (hc : ScalarValid i p g0 g1 j0 j1 u0 u1)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ} (k : ℕ)
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 350 ≤ S.card) (hz : z ∈ Icc p.a p.b)
    (hrank : (S.card : ℝ)/4 ≤ hardCoreMean G S z)
    (hmean : hardCoreMean G S z = (k : ℝ)) :
    DirectionBudgetGraph.Inputs p G S B z (hardCoreAvailableMean G S B z) k g0 g1 := by
  have ha : 0 < p.a := by
    rw [hc.a_match]
    exact_mod_cast (Stage350SourceTable.valid i).a_pos
  have hz0 := ha.trans_le hz.1
  have hlo : ((Stage350SourceTable.row i).a : ℝ) ≤ z := hc.a_match ▸ hz.1
  have hhi : z ≤ ((Stage350SourceTable.row i).b : ℝ) := hc.b_match ▸ hz.2
  have hb := Stage350SourceTable.actual_bounds i hB hG hn hlo hhi hrank
  have hs : p.start ≤ hardCoreAvailableMean G S B z := by
    rw [hc.start_match]
    exact Stage350SourceTable.start_le_available i hB hG hn hlo hhi hrank
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
  · exact Stage350SourceTable.actual_affine_tail_le_rate i j0 hB hG hn hlo hhi hrank
      hc.cap0 hp.alpha_pos.le hc.u0_nonneg hc.rate0
  · exact Stage350SourceTable.actual_affine_tail_le_rate i j1 hB hG hn hlo hhi hrank
      hc.cap1 hp.alpha1_pos.le hc.u1_nonneg hc.rate1
  · exact SmoothingInterval.asymmetry_le_endpoints hq.1 hq.2 hc.eta_left hc.eta_right
  · exact SmoothingInterval.cutoff_of_variance_lower hc.vmin_sixth hvmin
      hp.T_pos hp.T_lt_pi hc.cutoff_damping hc.cutoff_quartic
  · exact profile_valid_of_range hc.profile0 hp.vmin_pos hvmin (mul_pos hp.alpha_pos hp.start_pos)
      (mul_le_mul_of_nonneg_left hs hp.alpha_pos.le) hq.1 hq.2
  · exact profile_valid_of_range hc.profile1 hp.vmin_pos hvmin (mul_pos hp.alpha1_pos hp.start_pos)
      (mul_le_mul_of_nonneg_left hs hp.alpha1_pos.le) hq.1 hq.2

#print axioms actual_inputs
end ForestUnimodality.Stage350PlainDirectionInputs
