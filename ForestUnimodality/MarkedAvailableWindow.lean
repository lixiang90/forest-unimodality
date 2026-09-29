import ForestUnimodality.Stage99MarkedSourceLibrary

/-! Finite probability windows for all verified stage99 marked sources. -/
namespace ForestUnimodality.MarkedAvailableWindow

theorem reciprocal_profile {c D qa qb q : ℝ} (hqa : 0<qa)
    (hq : q∈Set.Icc qa qb)
    (ha : 1+c/qa≤D) (hb : 1+c/qb≤D) : 1+c/q≤D := by
  have hq0 := hqa.trans_le hq.1
  have hqb := hq0.trans_le hq.2
  have hca := (div_le_iff₀ hqa).mp (show c/qa≤D-1 by linarith)
  have hcb := (div_le_iff₀ hqb).mp (show c/qb≤D-1 by linarith)
  have hc : c≤(D-1)*q := by
    by_cases hd : 0≤D-1
    · exact hca.trans (mul_le_mul_of_nonneg_left hq.1 hd)
    · exact hcb.trans (mul_le_mul_of_nonpos_left hq.2 (le_of_not_ge hd))
  have hh := (div_le_iff₀ hq0).mpr hc
  linarith

structure Window where
  source : Fin 31
  qa : ℚ
  qb : ℚ
  D : ℚ

def Window.factor (w : Window) : ℚ :=
  2*(Stage99MarkedSourceLibrary.parameters w.source).A+
    (Stage99MarkedSourceLibrary.parameters w.source).C-1

def Window.Accepts (w : Window) : Prop :=
  0<w.qa ∧ w.qa≤w.qb ∧ w.qb<1 ∧
  (Stage99MarkedSourceLibrary.domain w.source).lower≤w.qa/(1-w.qa) ∧
  w.qb/(1-w.qb)≤(Stage99MarkedSourceLibrary.domain w.source).b ∧
  1+w.factor/w.qa≤w.D ∧ 1+w.factor/w.qb≤w.D

instance (w : Window) : Decidable w.Accepts := by
  unfold Window.Accepts
  infer_instance

def Window.check (w : Window) : Bool := decide w.Accepts

variable {V : Type*} [DecidableEq V]

theorem Window.actual_available_variance (w : Window) (hw : w.check=true)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hq : z/(1+z)∈Set.Icc (w.qa:ℝ) (w.qb:ℝ)) :
    hardCoreAvailableVariance G S B z≤(w.D:ℝ)*hardCoreAvailableMean G S B z := by
  have h : w.Accepts := of_decide_eq_true hw
  have hqa : (0:ℝ)<w.qa := by exact_mod_cast h.1
  have hqa1 : (w.qa:ℝ)<1 := by exact_mod_cast h.2.1.trans_lt h.2.2.1
  have hqb1 : (w.qb:ℝ)<1 := by exact_mod_cast h.2.2.1
  have hlow := (le_div_iff₀ (by positivity : 0<1+z)).mp hq.1
  have hhigh := (div_le_iff₀ (by positivity : 0<1+z)).mp hq.2
  have ha : (w.qa:ℝ)/(1-w.qa)≤z := by
    apply (div_le_iff₀ (by linarith : 0<1-(w.qa:ℝ))).mpr
    nlinarith
  have hb : z≤(w.qb:ℝ)/(1-w.qb) := by
    apply (le_div_iff₀ (by linarith : 0<1-(w.qb:ℝ))).mpr
    nlinarith
  have hlo : ((Stage99MarkedSourceLibrary.domain w.source).lower:ℝ)≤z :=
    (show ((Stage99MarkedSourceLibrary.domain w.source).lower:ℝ)≤(w.qa:ℝ)/(1-w.qa) by
      exact_mod_cast h.2.2.2.1).trans ha
  have hhi : z≤((Stage99MarkedSourceLibrary.domain w.source).b:ℝ) :=
    hb.trans (by exact_mod_cast h.2.2.2.2.1)
  have hs := hB.available_variance_le_of_source_certificate hG
    (ParametricSource.Domain.check_sound (Stage99MarkedSourceLibrary.domain_checked w.source)).lower_pos
    hlo hhi (Stage99MarkedSourceLibrary.parameters w.source).toReal
    ((Stage99MarkedSourceLibrary.parameters w.source).admissible_sound
      (Stage99MarkedSourceLibrary.parameters_checked w.source))
    (Stage99MarkedSourceLibrary.coefficients_nonneg w.source).1
    (Stage99MarkedSourceLibrary.source_valid w.source)
  have hc := reciprocal_profile (c:=(w.factor:ℝ)) (D:=(w.D:ℝ)) hqa hq
    (by exact_mod_cast h.2.2.2.2.2.1) (by exact_mod_cast h.2.2.2.2.2.2)
  simp only [Window.factor,Rat.cast_sub,Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_one] at hc
  exact hs.trans (mul_le_mul_of_nonneg_right hc (hardCoreAvailableMean_nonneg G S B hz.le))

#print axioms reciprocal_profile
#print axioms Window.actual_available_variance
end ForestUnimodality.MarkedAvailableWindow
