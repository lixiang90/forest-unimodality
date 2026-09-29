import ForestUnimodality.SourceOddsCapacity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! The true occupation-mass budget from heterogeneous forest messages.
The marked set is fixed; no maximization is performed under a tilt. -/
namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

noncomputable def sourcePhi (lower b p : ℝ) : ℝ :=
  (b / (1 + b)) / Real.log (1 + b) * max 0 (sourceLogCapacity lower p)

/-- A log chord on the full real probability interval, derived from concavity. -/
theorem source_probability_log_chord {b p : ℝ} (hb : 0 < b) (hp : 0 ≤ p)
    (hpq : p ≤ b / (1 + b)) :
    (b / (1 + b)) / Real.log (1 + b) * (-Real.log (1 - p)) ≤ p := by
  let q := b / (1 + b)
  have hB : 0 < 1 + b := by linarith
  have hq : 0 < q := div_pos hb hB
  have hq1 : q < 1 := (div_lt_one hB).mpr (by linarith)
  have hL : 0 < Real.log (1 + b) := Real.log_pos (by linarith)
  have hratio : p / q ≤ 1 := (div_le_one hq).mpr hpq
  have hc := (StrictConcaveOn.concaveOn strictConcaveOn_log_Ioi).2 (by norm_num : (1 : ℝ) ∈ Set.Ioi 0)
    (show 1 - q ∈ Set.Ioi 0 from sub_pos.mpr hq1)
    (show 0 ≤ 1 - p / q by linarith) (div_nonneg hp hq.le) (by ring : 1 - p / q + p / q = 1)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at hc
  have he : (1 - p / q) * 1 + p / q * (1 - q) = 1 - p := by field_simp; ring
  rw [he] at hc
  have hlog : Real.log (1 - q) = -Real.log (1 + b) := by
    have he : 1 - q = (1 + b)⁻¹ := by dsimp [q]; field_simp; ring
    rw [he, Real.log_inv]
  rw [hlog] at hc
  have hc' : p * (-Real.log (1 + b)) ≤ q * Real.log (1 - p) := by
    calc
      _ = q * (p / q * (-Real.log (1 + b))) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hc hq.le
  change q / Real.log (1 + b) * (-Real.log (1 - p)) ≤ p
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hL).mpr
  linarith

theorem SourceMessages.probability_le_bound {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    (hactivity : ∀ x ∈ S, 0 < activity x ∧ activity x ≤ b) {x : V} (hx : x ∈ S) :
    p x ≤ b / (1 + b) := by
  have hb : 0 < b := (hactivity x hx).1.trans_le (hactivity x hx).2
  have ho := (h.odds_le_activity (fun y hy => (hactivity y hy).1.le) hx).trans (hactivity x hx).2
  have hp1 := sub_pos.mpr (h.probability x hx).2
  have ho' := (div_le_iff₀ hp1).mp ho
  apply (le_div_iff₀ (by linarith : 0 < 1 + b)).mpr
  nlinarith

theorem SourceMessages.lower_log_capacity_le_children {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {lower : ℝ} (hlower : 0 < lower)
    (hactivity : ∀ x ∈ S, lower ≤ activity x) {x : V} (hx : x ∈ S) :
    sourceLogCapacity lower (p x) ≤ ∑ y ∈ sourceChildren S parent x, -Real.log (1 - p y) := by
  have hact : ∀ y ∈ S, 0 < activity y := fun y hy => hlower.trans_le (hactivity y hy)
  have hp := h.probability_pos hact hx
  have h1 := sub_pos.mpr (h.probability x hx).2
  have he := h.log_odds hact hx
  have hl := Real.log_le_log hlower (hactivity x hx)
  unfold sourceLogCapacity
  rw [Real.log_div (mul_ne_zero hlower.ne' h1.ne') hp.ne', Real.log_mul hlower.ne' h1.ne']
  simp only [sum_neg_distrib]
  linarith

/-- Actual children carry at least phi(p) total occupation-message mass. -/
theorem SourceMessages.phi_le_child_probability {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {lower b : ℝ} (hlower : 0 < lower)
    (hactivity : ∀ x ∈ S, lower ≤ activity x ∧ activity x ≤ b) {x : V} (hx : x ∈ S) :
    sourcePhi lower b (p x) ≤ ∑ y ∈ sourceChildren S parent x, p y := by
  have hb : 0 < b := (hlower.trans_le (hactivity x hx).1).trans_le (hactivity x hx).2
  have hact : ∀ y ∈ S, 0 < activity y ∧ activity y ≤ b :=
    fun y hy => ⟨hlower.trans_le (hactivity y hy).1, (hactivity y hy).2⟩
  have hlognonneg : 0 ≤ ∑ y ∈ sourceChildren S parent x, -Real.log (1 - p y) := by
    apply sum_nonneg
    intro y hy
    have hp := h.probability y (mem_filter.mp hy).1
    exact neg_nonneg.mpr (Real.log_nonpos (sub_nonneg.mpr hp.2.le) (by linarith))
  have hmax := max_le hlognonneg (h.lower_log_capacity_le_children hlower (fun y hy => (hactivity y hy).1) hx)
  have hfactor : 0 ≤ (b / (1 + b)) / Real.log (1 + b) :=
    div_nonneg (div_nonneg hb.le (by linarith)) (Real.log_pos (by linarith)).le
  apply (mul_le_mul_of_nonneg_left hmax hfactor).trans
  rw [mul_sum]
  exact sum_le_sum (fun y hy => source_probability_log_chord hb
    (h.probability y (mem_filter.mp hy).1).1 (h.probability_le_bound hact (mem_filter.mp hy).1))

/-- Occupation-weighted parent/child cancellation, in direct marginal form. -/
theorem SourceMessages.phi_budget {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {lower b : ℝ} (hlower : 0 < lower)
    (hactivity : ∀ x ∈ S, lower ≤ activity x ∧ activity x ≤ b) :
    (∑ x ∈ S, (heterogeneousMarginal G S activity x * (1 + sourcePhi lower b (p x)) - p x)) ≤ 0 := by
  have hnonneg : ∀ y ∈ S, 0 ≤ activity y := fun y hy => (hlower.trans_le (hactivity y hy).1).le
  have hlocal := sum_le_sum (s := S) (fun x hx =>
    mul_le_mul_of_nonneg_left (h.phi_le_child_probability hlower hactivity hx)
      (heterogeneousMarginal_mem_Icc G S activity hnonneg x).1)
  have htransfer := h.sum_parent_marginal p
  have he : (∑ x ∈ S, sourceParentMass G S activity (parent x) * p x) =
      ∑ x ∈ S, (p x - heterogeneousMarginal G S activity x) := by
    apply sum_congr rfl
    intro x hx
    nlinarith [h.marginal x hx]
  rw [he] at htransfer
  have hout : (∑ x ∈ S, (heterogeneousMarginal G S activity x * (1 + sourcePhi lower b (p x)) - p x)) =
      (∑ x ∈ S, heterogeneousMarginal G S activity x * sourcePhi lower b (p x)) -
        (∑ x ∈ S, (p x - heterogeneousMarginal G S activity x)) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro x _
    ring
  rw [hout]
  linarith

noncomputable def sourcePhiBudget (G : SimpleGraph V) (S : Finset V) (activity p : V → ℝ)
    (lower b : ℝ) : ℝ :=
  ∑ x ∈ S, p x * ((heterogeneousMarginal G S activity x / p x) * (1 + sourcePhi lower b (p x)) - 1)

theorem SourceMessages.phi_budget_scaled {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {lower b : ℝ} (hlower : 0 < lower)
    (hactivity : ∀ x ∈ S, lower ≤ activity x ∧ activity x ≤ b) :
    sourcePhiBudget G S activity p lower b ≤ 0 := by
  convert h.phi_budget hlower hactivity using 1
  unfold sourcePhiBudget
  apply sum_congr rfl
  intro x hx
  have hp : p x ≠ 0 := (h.probability_pos (fun y hy => hlower.trans_le (hactivity y hy).1) hx).ne'
  field_simp

/-- Actual finite forests provide phi along with the real marked moments. -/
theorem exists_forest_source_phi (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V)
    (activity a : V → ℝ) {lower b : ℝ} (hlower : 0 < lower)
    (hactivity : ∀ x ∈ S, lower ≤ activity x ∧ activity x ≤ b) :
    ∃ parent p d, SourceMessages G S activity a parent p d ∧
      heterogeneousMean G S activity (markedSum a) = ∑ x ∈ S, p x * d x ∧
      heterogeneousVariance G S activity (markedSum a) =
        (∑ x ∈ S, heterogeneousMarginal G S activity x * (1 - p x) * d x ^ 2) ∧
      sourcePhiBudget G S activity p lower b ≤ 0 := by
  obtain ⟨parent, p, d, hm, hmean, hvar⟩ := exists_forest_source_messages_moments G hG S activity a
    (fun x hx => (hlower.trans_le (hactivity x hx).1).le)
  exact ⟨parent, p, d, hm, hmean, hvar, hm.phi_budget_scaled hlower hactivity⟩


theorem SourceMessages.marginal_le_probability {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) (hactivity : ∀ x ∈ S, 0 ≤ activity x)
    {x : V} (hx : x ∈ S) : heterogeneousMarginal G S activity x ≤ p x := by
  have hpar : 0 ≤ sourceParentMass G S activity (parent x) := by
    cases parent x with
    | none => exact le_rfl
    | some y => exact (heterogeneousMarginal_mem_Icc G S activity hactivity y).1
  have hp := (h.probability x hx).1
  nlinarith [h.marginal x hx]

/-- A specified child's factor remains in its parent's odds product. -/
theorem SourceMessages.child_product_le_factor {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {x y : V} (hy : y ∈ sourceChildren S parent x) :
    sourceChildProduct S parent p x ≤ 1 - p y := by
  classical
  have hp := h.probability y (mem_filter.mp hy).1
  have hr : (∏ z ∈ (sourceChildren S parent x).erase y, (1 - p z)) ≤ 1 := by
    apply prod_le_one
    · intro z hz
      exact sub_nonneg.mpr (h.probability z (mem_filter.mp (mem_of_mem_erase hz)).1).2.le
    · intro z hz
      have hpz := (h.probability z (mem_filter.mp (mem_of_mem_erase hz)).1).1
      linarith
  unfold sourceChildProduct
  rw [← mul_prod_erase _ _ hy]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hr (sub_nonneg.mpr hp.2.le)

/-- The true retention interval used by the scalar source certificates. -/
theorem SourceMessages.retention_bounds {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    (hactivity : ∀ x ∈ S, 0 < activity x ∧ activity x ≤ b) {x : V} (hx : x ∈ S) :
    1 / (1 + b * (1 - p x)) ≤ heterogeneousMarginal G S activity x / p x ∧
      heterogeneousMarginal G S activity x / p x ≤ 1 := by
  have hp := h.probability_pos (fun y hy => (hactivity y hy).1) hx
  have hp1 := sub_pos.mpr (h.probability x hx).2
  have hb : 0 < b := (hactivity x hx).1.trans_le (hactivity x hx).2
  have hB : 0 < 1 + b * (1 - p x) := by positivity
  have hnonneg : ∀ y ∈ S, 0 ≤ activity y := fun y hy => (hactivity y hy).1.le
  have hratio : heterogeneousMarginal G S activity x / p x =
      1 - sourceParentMass G S activity (parent x) := by
    rw [h.marginal x hx]
    exact mul_div_cancel_left₀ _ hp.ne'
  refine ⟨?_, (div_le_one hp).mpr (h.marginal_le_probability hnonneg hx)⟩
  have hparent : sourceParentMass G S activity (parent x) ≤
      b * (1 - p x) / (1 + b * (1 - p x)) := by
    cases he : parent x with
    | none => exact div_nonneg (mul_nonneg hb.le hp1.le) hB.le
    | some y =>
      have hy := (h.parent_mem x hx y he).1
      have hxy : x ∈ sourceChildren S parent y := mem_filter.mpr ⟨hx, he⟩
      have hprod := h.child_product_le_factor hxy
      have hodds : p y / (1 - p y) ≤ b * (1 - p x) := by
        rw [h.odds_eq hy]
        exact (mul_le_mul_of_nonneg_left hprod (hactivity y hy).1.le).trans
          (mul_le_mul_of_nonneg_right (hactivity y hy).2 hp1.le)
      have hpy1 := sub_pos.mpr (h.probability y hy).2
      have hodds' := (div_le_iff₀ hpy1).mp hodds
      have hpy : p y ≤ b * (1 - p x) / (1 + b * (1 - p x)) := by
        apply (le_div_iff₀ hB).mpr
        nlinarith
      exact (h.marginal_le_probability hnonneg hy).trans hpy
  have he : 1 / (1 + b * (1 - p x)) = 1 - b * (1 - p x) / (1 + b * (1 - p x)) := by field_simp; ring
  rw [hratio, he]
  linarith

/-- At the maximal possible message p=q the true response is the source mark;
scalar source certificates must treat this boundary as a leaf response. -/
theorem SourceMessages.response_at_probability_endpoint {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    (hactivity : ∀ x ∈ S, 0 < activity x ∧ activity x ≤ b) {x : V} (hx : x ∈ S)
    (he : p x = b / (1 + b)) : d x = a x := by
  have hb : 0 < b := (hactivity x hx).1.trans_le (hactivity x hx).2
  have hB : 0 < 1 + b := by linarith
  apply h.eq_mark_of_capacity_zero hactivity hx
  unfold sourceLogCapacity
  rw [he]
  have heq : b * (1 - b / (1 + b)) / (b / (1 + b)) = 1 := by field_simp; ring
  rw [heq, Real.log_one]

#print axioms source_probability_log_chord
#print axioms SourceMessages.phi_le_child_probability
#print axioms SourceMessages.phi_budget_scaled
#print axioms SourceMessages.retention_bounds
#print axioms SourceMessages.response_at_probability_endpoint
#print axioms exists_forest_source_phi
end ForestUnimodality

