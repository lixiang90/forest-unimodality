import ForestUnimodality.Stage80ConstantLibrary
import ForestUnimodality.MeanMatchedSourceBudget

/-! Exact-constant source consequences for finite kernel probability windows.
These statements quantify over actual forests of every order. -/
namespace ForestUnimodality.Stage80ConstantWindow

structure Window where
  source : Fin 20
  qa : ℚ
  qb : ℚ
  R : ℚ
  vmax : ℚ

def Window.Accepts (w : Window) : Prop :=
  0<w.qa ∧ w.qa≤w.qb ∧ w.qb<1 ∧
  (Stage80ConstantLibrary.domain w.source).lower≤w.qa/(1-w.qa) ∧
  w.qb/(1-w.qb)≤(Stage80ConstantLibrary.domain w.source).b ∧
  0≤w.R ∧ Stage80ConstantLibrary.factor w.source/(1-w.qb)-1≤w.R ∧
  ((w.qb≤1/2 ∧ w.qb*(1-w.qb)≤w.vmax) ∨
    (1/2≤w.qa ∧ w.qa*(1-w.qa)≤w.vmax) ∨ 1/4≤w.vmax)

instance (w : Window) : Decidable w.Accepts := by
  unfold Window.Accepts
  infer_instance

def Window.check (w : Window) : Bool := decide w.Accepts

theorem Window.activity_bounds (w : Window) (hw : w.check=true) {z : ℝ}
    (hz : 0<z) (hq : z/(1+z)∈Set.Icc (w.qa:ℝ) (w.qb:ℝ)) :
    ((Stage80ConstantLibrary.domain w.source).lower:ℝ)≤z ∧
      z≤((Stage80ConstantLibrary.domain w.source).b:ℝ) := by
  have h : w.Accepts := of_decide_eq_true hw
  have hqa : (w.qa:ℝ)<1 := by exact_mod_cast h.2.1.trans_lt h.2.2.1
  have hqb : (w.qb:ℝ)<1 := by exact_mod_cast h.2.2.1
  have hlo := (le_div_iff₀ (by positivity : 0<1+z)).mp hq.1
  have hhi := (div_le_iff₀ (by positivity : 0<1+z)).mp hq.2
  have hl : (w.qa:ℝ)/(1-w.qa)≤z := by
    apply (div_le_iff₀ (by linarith : 0<1-(w.qa:ℝ))).mpr
    nlinarith
  have hh : z≤(w.qb:ℝ)/(1-w.qb) := by
    apply (le_div_iff₀ (by linarith : 0<1-(w.qb:ℝ))).mpr
    nlinarith
  constructor
  · have hd : ((Stage80ConstantLibrary.domain w.source).lower:ℝ)≤(w.qa:ℝ)/(1-w.qa) := by
      exact_mod_cast h.2.2.2.1
    exact hd.trans hl
  · exact hh.trans (by exact_mod_cast h.2.2.2.2.1)

theorem Window.variance_cap (w : Window) (hw : w.check=true) {q : ℝ}
    (hq : q∈Set.Icc (w.qa:ℝ) (w.qb:ℝ)) : q*(1-q)≤(w.vmax:ℝ) := by
  have h : w.Accepts := of_decide_eq_true hw
  rcases h.2.2.2.2.2.2.2 with hc | hc | hc
  · have hqb : (w.qb:ℝ)≤1/2 := by
      have hh := (Rat.cast_le (K:=ℝ)).mpr hc.1
      norm_num at hh ⊢
      exact hh
    have hb : (w.qb:ℝ)*(1-w.qb)≤w.vmax := by exact_mod_cast hc.2
    nlinarith [mul_nonneg (sub_nonneg.mpr hq.2) (show 0≤1-(w.qb:ℝ)-q by linarith [hq.2])]
  · have hqa : (1/2:ℝ)≤w.qa := by
      have hh := (Rat.cast_le (K:=ℝ)).mpr hc.1
      norm_num at hh ⊢
      exact hh
    have hb : (w.qa:ℝ)*(1-w.qa)≤w.vmax := by exact_mod_cast hc.2
    nlinarith [mul_nonneg (sub_nonneg.mpr hq.1) (show 0≤q+(w.qa:ℝ)-1 by linarith [hq.1])]
  · have hb : (1/4:ℝ)≤w.vmax := by
      have hh := (Rat.cast_le (K:=ℝ)).mpr hc
      norm_num at hh ⊢
      exact hh
    nlinarith [sq_nonneg (q-1/2)]

variable {V : Type*} [DecidableEq V]

theorem Window.centered_variance (w : Window) (hw : w.check=true)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hq : z/(1+z)∈Set.Icc (w.qa:ℝ) (w.qb:ℝ)) :
    hardCoreLayerMeanVariance G S B z≤
      (w.R:ℝ)*(z/(1+z)*(1-z/(1+z)))*hardCoreAvailableMean G S B z := by
  have h : w.Accepts := of_decide_eq_true hw
  have hab := w.activity_bounds hw hz hq
  have hs := SelectionSource.Parameters.check_sound (Stage80ConstantLibrary.parameters_checked w.source)
  have hc : (0:ℝ)≤Stage80ConstantLibrary.factor w.source := by
    simp only [Stage80ConstantLibrary.factor, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]
    exact add_nonneg hs.2.1 (mul_nonneg (by norm_num) hs.2.2)
  exact MeanMatchedSourceBudget.centered_variance_bound hB.subset hB.independent hz hq.2
    (by exact_mod_cast h.2.2.1) hc (by exact_mod_cast h.2.2.2.2.2.2.1)
    (Stage80ConstantLibrary.actual_variance_le_mass w.source hB hG hab.1 hab.2)

theorem Window.total_variance (w : Window) (hw : w.check=true)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hq : z/(1+z)∈Set.Icc (w.qa:ℝ) (w.qb:ℝ)) :
    hardCoreVariance G S z≤
      (z/(1+z)*(1-z/(1+z))+(w.R*w.vmax:ℚ))*hardCoreAvailableMean G S B z+0 := by
  have h : w.Accepts := of_decide_eq_true hw
  have hc := w.centered_variance hw hB hG hz hq
  have hv := w.variance_cap hw hq
  have hm := hardCoreAvailableMean_nonneg G S B hz.le
  have hR : (0:ℝ)≤w.R := by exact_mod_cast h.2.2.2.2.2.1
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hR) hm
  have he := hardCoreVariance_eq_layer_variance G S B hB.subset hB.independent hz
  push_cast
  nlinarith

#print axioms Window.centered_variance
#print axioms Window.total_variance
end ForestUnimodality.Stage80ConstantWindow
