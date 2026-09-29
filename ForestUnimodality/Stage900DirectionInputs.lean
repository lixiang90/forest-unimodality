import ForestUnimodality.Stage900SourceTable
import ForestUnimodality.DirectionBudgetGraph
import ForestUnimodality.ImprovedSourceTail
import ForestUnimodality.SmoothingInterval

/-! Scalar obligations sufficient to discharge the actual stage-900
direction inputs. Their finite instances are checked in a separate module. -/
namespace ForestUnimodality.Stage900DirectionInputs
open Set DirectionBudget ReciprocalGradientBudget

noncomputable def qLower (p : Parameters) : ℝ := p.a / (1 + p.a)
noncomputable def qUpper (p : Parameters) : ℝ := p.b / (1 + p.b)
noncomputable def pathLower (p : Parameters) : ℝ := p.a / (33 / 20 + p.a)
noncomputable def pathVariance (p : Parameters) : ℝ :=
  min (pathLower p * (1 - pathLower p)) (qUpper p * (1 - qUpper p))

def ProfileRange (g : GradientProfile) (lo hi v threshold : ℝ) : Prop :=
  match g with
  | .universal => True
  | .thirtyOne => 3 / 10 ≤ lo ∧ hi ≤ 7 / 10
  | .general i => 3 / 10 ≤ lo ∧ hi ≤ 7 / 10 ∧ (BinomialGradientTable.scale i)^2 ≤ threshold*v
  | .near i => 9 / 20 ≤ lo ∧ hi ≤ 11 / 20 ∧ (BinomialGradientTable.scale i)^2 ≤ threshold*v

-- Materialize the equation lemmas in their defining module, so later
-- independent certificate modules never create competing copies.
#print equations ProfileRange

theorem profile_valid_of_range {g : GradientProfile} {lo hi q v start threshold : ℝ}
    (h : ProfileRange g lo hi v start) (hv : 0 < v) (hvq : v ≤ q*(1-q))
    (ht : 0 < start) (hst : start ≤ threshold) (hlo : lo ≤ q) (hhi : q ≤ hi) :
    g.Valid q v threshold := by
  refine ⟨hv, hvq, ht.trans_le hst, ?_⟩
  cases g with
  | universal => trivial
  | thirtyOne => exact ⟨h.1.trans hlo, hhi.trans h.2⟩
  | general i =>
    exact ⟨h.1.trans hlo, hhi.trans h.2.1,
      h.2.2.trans (mul_le_mul_of_nonneg_right hst hv.le)⟩
  | near i =>
    exact ⟨h.1.trans hlo, hhi.trans h.2.1,
      h.2.2.trans (mul_le_mul_of_nonneg_right hst hv.le)⟩

structure ScalarValid (i : Fin 28) (p : Parameters) (g0 g1 : GradientProfile)
    (u0 u1 : ℝ) : Prop where
  a_match : p.a = ((Stage900SourceTable.base i).lower : ℝ)
  b_match : p.b = ((Stage900SourceTable.base i).upper : ℝ)
  start_match : p.start = ((Stage900SourceTable.row i).start : ℝ)
  D_match : p.D = ((Stage900SourceTable.row i).D : ℝ)
  R_match : p.R = ((Stage900SourceTable.row i).R : ℝ)
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
  u0_nonneg : 0 ≤ u0
  u0_upper : u0 ≤ 1/2
  u1_nonneg : 0 ≤ u1
  u1_upper : u1 ≤ 1/2
  rate0 : p.rate0 ≤ qLower p*(1-p.alpha)*u0-
    (((Stage900SourceTable.row i).Cs : ℝ)-p.alpha*pathVariance p)*u0^2/2
  rate1 : p.rate1 ≤ qLower p*(1-p.alpha1)*u1-
    (((Stage900SourceTable.row i).Cs : ℝ)-p.alpha1*pathVariance p)*u1^2/2

variable {V : Type*} [DecidableEq V]

theorem corrected_tail (p : Parameters) (G : SimpleGraph V) (S B : Finset V)
    (hBS : B ⊆ S) (hB : G.IsIndepSet (B : Set V)) {z C alpha u rate : ℝ}
    (ha : 0 < p.a) (hz : z ∈ Icc p.a p.b) (halpha : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hu : 0 ≤ u) (hu1 : u ≤ 1/2)
    (hsource : ∀ t ≥ 0, heterogeneousVariance G S
      (independentTiltActivities B z (Real.exp (-t)))
      (fun J => ((J ∩ B).card : ℝ)) ≤ C * hardCoreAvailableMean G S B z)
    (hrate : rate ≤ qLower p*(1-alpha)*u-(C-alpha*pathVariance p)*u^2/2) :
    hardCoreAvailableLowerTail G S B z (alpha*hardCoreAvailableMean G S B z) ≤
      Real.exp (-rate*hardCoreAvailableMean G S B z) := by
  have hz0 := ha.trans_le hz.1
  have hq := SmoothingInterval.activity_fraction_bounds ha.le hz.1 hz.2
  have hlo : pathLower p ≤ z / (33/20+z) := by
    unfold pathLower
    apply (div_le_div_iff₀ (by positivity : 0 < 33/20+p.a)
      (by positivity : 0 < 33/20+z)).mpr
    nlinarith [hz.1]
  exact hardCoreAvailableLowerTail_le_endpoint_corrected_rate G S B hBS hB
    hz0 hu hu1 (by norm_num) exp_half_le_33_20 hlo hq.2
    (min_le_left _ _) (min_le_right _ _) halpha halpha1 hq.1
    (fun t ht => hsource t ht.1) hrate

/-- Once the finite scalar row is checked, no variance, tail, smoothing or
profile hypothesis remains: the input is one actual maximum-marginal set. -/
theorem actual_inputs (i : Fin 28) (p : Parameters) (hp : p.Valid)
    (g0 g1 : GradientProfile) (u0 u1 : ℝ) (hc : ScalarValid i p g0 g1 u0 u1)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ} (k : ℕ)
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 900 ≤ S.card) (hz : z ∈ Icc p.a p.b)
    (hrank : (S.card : ℝ)/4 ≤ hardCoreMean G S z)
    (hmean : hardCoreMean G S z = (k : ℝ)) :
    DirectionBudgetGraph.Inputs p G S B z (hardCoreAvailableMean G S B z) k g0 g1 := by
  have ha : 0 < p.a := by
    rw [hc.a_match]
    exact_mod_cast (Stage900SourceTable.valid i).lower_pos
  have hz0 := ha.trans_le hz.1
  have hlo : ((Stage900SourceTable.base i).lower : ℝ) ≤ z := hc.a_match ▸ hz.1
  have hhi : z ≤ ((Stage900SourceTable.base i).upper : ℝ) := hc.b_match ▸ hz.2
  have hb := Stage900SourceTable.actual_bounds i hB hG hn hlo hhi hrank
  have hs : p.start ≤ hardCoreAvailableMean G S B z := by
    rw [hc.start_match]
    exact Stage900SourceTable.start_le_available i hB hG hn hlo hhi hrank
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
  · exact corrected_tail p G S B hB.subset hB.independent ha hz hp.alpha_pos.le hp.alpha_lt.le
      hc.u0_nonneg hc.u0_upper hb.tilt_variance hc.rate0
  · exact corrected_tail p G S B hB.subset hB.independent ha hz hp.alpha1_pos.le
      (hp.alpha1_le.trans hp.alpha_lt.le) hc.u1_nonneg hc.u1_upper hb.tilt_variance hc.rate1
  · exact SmoothingInterval.asymmetry_le_endpoints hq.1 hq.2 hc.eta_left hc.eta_right
  · exact SmoothingInterval.cutoff_of_variance_lower hc.vmin_sixth hvmin
      hp.T_pos hp.T_lt_pi hc.cutoff_damping hc.cutoff_quartic
  · exact profile_valid_of_range hc.profile0 hp.vmin_pos hvmin (mul_pos hp.alpha_pos hp.start_pos)
      (mul_le_mul_of_nonneg_left hs hp.alpha_pos.le) hq.1 hq.2
  · exact profile_valid_of_range hc.profile1 hp.vmin_pos hvmin (mul_pos hp.alpha1_pos hp.start_pos)
      (mul_le_mul_of_nonneg_left hs hp.alpha1_pos.le) hq.1 hq.2

#print axioms corrected_tail
#print axioms actual_inputs
end ForestUnimodality.Stage900DirectionInputs
