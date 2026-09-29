import ForestUnimodality.AnalyticInterval
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Continuous infinite-tail budget checks. The lower endpoint is sufficient
only after each exact power/exponential cost is proved decreasing on the
entire half-line. Real powers include square roots and inverse powers. -/
namespace ForestUnimodality.UnboundedBudget
open Set Finset

noncomputable def powerExpCost (p rate m : ℝ) : ℝ := m^p*Real.exp (-rate*m)

theorem hasDerivAt_powerExpCost (p rate : ℝ) {m : ℝ} (hm : 0 < m) :
    HasDerivAt (powerExpCost p rate)
      (m^(p-1)*Real.exp (-rate*m)*(p-rate*m)) m := by
  have hd := (Real.hasDerivAt_rpow_const (p := p) (Or.inl (ne_of_gt hm))).mul
    (((hasDerivAt_id m).const_mul (-rate)).exp)
  apply hd.congr_deriv
  simp only [id_eq, mul_one]
  rw [Real.rpow_sub hm, Real.rpow_one]
  field_simp
  ring

theorem powerExpCost_antitoneOn {p rate start : ℝ}
    (hs : 0 < start) (hr : 0 ≤ rate) (hthreshold : p ≤ rate*start) :
    AntitoneOn (powerExpCost p rate) (Ici start) := by
  have hd (m : ℝ) (hm : m ∈ Ici start) := hasDerivAt_powerExpCost p rate (hs.trans_le hm)
  apply antitoneOn_of_deriv_nonpos (convex_Ici start)
  · intro m hm; exact (hd m hm).continuousAt.continuousWithinAt
  · intro m hm; exact (hd m (interior_subset hm)).differentiableAt.differentiableWithinAt
  · intro m hm
    have hms := interior_subset hm
    rw [(hd m hms).deriv]
    have hc : p-rate*m ≤ 0 := by
      have h := mul_le_mul_of_nonneg_left hms hr
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (Real.rpow_nonneg (hs.trans_le hms).le _) (Real.exp_pos _).le) hc

noncomputable def budget {ι : Type*} (s : Finset ι) (base : ℝ)
    (price power rate : ι → ℝ) (m : ℝ) : ℝ :=
  base-∑ i ∈ s, price i*powerExpCost (power i) (rate i) m

theorem budget_monotoneOn {ι : Type*} (s : Finset ι) (base : ℝ)
    (price power rate : ι → ℝ) {start : ℝ} (hs : 0 < start)
    (hprice : ∀ i ∈ s, 0 ≤ price i) (hrate : ∀ i ∈ s, 0 ≤ rate i)
    (hthreshold : ∀ i ∈ s, power i ≤ rate i*start) :
    MonotoneOn (budget s base price power rate) (Ici start) := by
  intro x hx y hy hxy
  apply sub_le_sub_left
  apply sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left
    (powerExpCost_antitoneOn hs (hrate i hi) (hthreshold i hi) hx hy hxy) (hprice i hi)

theorem budget_pos_of_start {ι : Type*} (s : Finset ι) (base : ℝ)
    (price power rate : ι → ℝ) {start m : ℝ} (hs : 0 < start)
    (hprice : ∀ i ∈ s, 0 ≤ price i) (hrate : ∀ i ∈ s, 0 ≤ rate i)
    (hthreshold : ∀ i ∈ s, power i ≤ rate i*start)
    (hpositive : 0 < budget s base price power rate start) (hm : start ≤ m) :
    0 < budget s base price power rate m :=
  hpositive.trans_le (budget_monotoneOn s base price power rate hs hprice hrate hthreshold
    (show start ∈ Ici start by simp) (show m ∈ Ici start by exact hm) hm)

theorem matchingRatio_monotone {c x y : ℝ} (hc : 0 ≤ c) (hx : 0 < x) (hxy : x ≤ y) :
    x/(x+c) ≤ y/(y+c) := by
  apply (div_le_div_iff₀ (add_pos_of_pos_of_nonneg hx hc)
    (add_pos_of_pos_of_nonneg (hx.trans_le hxy) hc)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hxy hc]

theorem matchingFactor_monotone {c p x y : ℝ}
    (hc : 0 ≤ c) (hp : 0 ≤ p) (hx : 0 < x) (hxy : x ≤ y) :
    (x/(x+c))^p ≤ (y/(y+c))^p :=
  Real.rpow_le_rpow (by positivity) (matchingRatio_monotone hc hx hxy) hp

theorem badEndpoint_antitone {α c x y : ℝ}
    (hα : α ≤ 1) (hc : 0 ≤ c) (hx : 0 < x) (hxy : x ≤ y) :
    (α*y+c)/(y+c) ≤ (α*x+c)/(x+c) := by
  apply (div_le_div_iff₀ (add_pos_of_pos_of_nonneg (hx.trans_le hxy) hc)
    (add_pos_of_pos_of_nonneg hx hc)).mpr
  have h := mul_nonneg (mul_nonneg (sub_nonneg.mpr hxy) hc) (sub_nonneg.mpr hα)
  nlinarith

theorem bridgeRatio_antitone {α x y : ℝ} (hα : 0 < α) (hx : 1 < α*x) (hxy : x ≤ y) :
    α*y/(α*y-1) ≤ α*x/(α*x-1) := by
  have hy : 1 < α*y := hx.trans_le (mul_le_mul_of_nonneg_left hxy hα.le)
  apply (div_le_div_iff₀ (sub_pos.mpr hy) (sub_pos.mpr hx)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hxy hα.le]

#print axioms powerExpCost_antitoneOn
#print axioms budget_pos_of_start
#print axioms matchingFactor_monotone
#print axioms badEndpoint_antitone
end ForestUnimodality.UnboundedBudget
