import ForestUnimodality.PiecewiseFlowZeroSlope
import ForestUnimodality.ExpEnclosure

/-! Exact rational witnesses for one positive-slope flow comparison. The
endpoint and integral can use different certificates and affine sources.
The source variance inequality is supplied separately for the whole step. -/
namespace ForestUnimodality.FlowComparisonCertificate

structure Certificate where
  decay : ExpEnclosure.PowerCertificate
  decayLo : ℚ
  decayHi : ℚ
  interceptQuotient : ℚ
  integralFactor : ℚ

def Certificate.endBound (c : Certificate) (L : ℚ) : ℚ :=
  L*c.decayLo-c.interceptQuotient*(1-c.decayLo)
def Certificate.areaBound (c : Certificate) (L duration : ℚ) : ℚ :=
  L*c.integralFactor-c.interceptQuotient*(duration-c.integralFactor)

def Certificate.Accepts (c : Certificate) (L D C duration : ℚ) : Prop :=
  0≤L ∧ 0≤D ∧ 0<C ∧ 0≤duration ∧
  c.decay.check (-C*duration) c.decayLo c.decayHi=true ∧
  D≤c.interceptQuotient*C ∧ 0≤c.integralFactor ∧ c.integralFactor≤duration ∧
  C*c.integralFactor≤1-c.decayHi

instance (c : Certificate) (L D C duration : ℚ) : Decidable (c.Accepts L D C duration) := by
  unfold Certificate.Accepts
  infer_instance

def Certificate.check (c : Certificate) (L D C duration : ℚ) : Bool :=
  decide (c.Accepts L D C duration)

theorem Certificate.check_sound {c : Certificate} {L D C duration : ℚ}
    (hc : c.check L D C duration=true) :
    (c.endBound L:ℝ)≤PiecewiseFlowLaplace.endLower L D C duration ∧
    (c.areaBound L duration:ℝ)≤PiecewiseFlowLaplace.integralLower L D C duration := by
  have h : c.Accepts L D C duration := of_decide_eq_true hc
  rcases h with ⟨hL,hD,hC,ht,hexp,hac,hf0,hft,hf⟩
  have hLR : (0:ℝ)≤L := by exact_mod_cast hL
  have hDR : (0:ℝ)≤D := by exact_mod_cast hD
  have hCR : (0:ℝ)<C := by exact_mod_cast hC
  have htR : (0:ℝ)≤duration := by exact_mod_cast ht
  have hacR : (D:ℝ)/C≤c.interceptQuotient := by
    apply (div_le_iff₀ hCR).mpr
    exact_mod_cast hac
  have hftR : (c.integralFactor:ℝ)≤duration := by exact_mod_cast hft
  have hfR : (C:ℝ)*c.integralFactor≤1-(c.decayHi:ℝ) := by exact_mod_cast hf
  have he := c.decay.check_sound hexp
  push_cast at he
  have he1 : Real.exp (-(C:ℝ)*duration)≤1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  have helo1 := he.1.trans he1
  have hdc : (0:ℝ)≤(D:ℝ)/C := div_nonneg hDR hCR.le
  have hfactor : (c.integralFactor:ℝ)≤AffineLaplace.decayIntegral C duration := by
    unfold AffineLaplace.decayIntegral
    apply (le_div_iff₀ hCR).mpr
    linarith [he.2]
  constructor
  · have h₁ := mul_nonneg (sub_nonneg.mpr hacR) (sub_nonneg.mpr helo1)
    have h₂ := mul_nonneg (add_nonneg hLR hdc) (sub_nonneg.mpr he.1)
    simp only [Certificate.endBound,Rat.cast_sub,Rat.cast_mul,Rat.cast_one,
      PiecewiseFlowLaplace.endLower]
    nlinarith
  · have h₁ := mul_nonneg (sub_nonneg.mpr hacR) (sub_nonneg.mpr hftR)
    have h₂ := mul_nonneg (add_nonneg hLR hdc) (sub_nonneg.mpr hfactor)
    simp only [Certificate.areaBound,Rat.cast_sub,Rat.cast_mul,
      PiecewiseFlowLaplace.integralLower]
    nlinarith

theorem Certificate.clamped_sound {c : Certificate} {L D C duration next area : ℚ}
    (hc : c.check L D C duration=true)
    (hend : next≤max 0 (c.endBound L)) (harea : area≤max 0 (c.areaBound L duration)) :
    (next:ℝ)≤max 0 (PiecewiseFlowZeroSlope.endLower L D C duration) ∧
    (area:ℝ)≤max 0 (PiecewiseFlowZeroSlope.integralLower L D C duration) := by
  have hh := c.check_sound hc
  have h : c.Accepts L D C duration := of_decide_eq_true hc
  have hC : (C:ℝ)≠0 := ne_of_gt (by exact_mod_cast h.2.2.1 : (0:ℝ)<C)
  have he : (next:ℝ)≤max 0 (c.endBound L:ℝ) := by exact_mod_cast hend
  have ha : (area:ℝ)≤max 0 (c.areaBound L duration:ℝ) := by exact_mod_cast harea
  simp only [PiecewiseFlowZeroSlope.endLower,PiecewiseFlowZeroSlope.integralLower,if_neg hC]
  exact ⟨he.trans (max_le_max (le_refl 0) hh.1),ha.trans (max_le_max (le_refl 0) hh.2)⟩

#print axioms Certificate.check_sound
#print axioms Certificate.clamped_sound
end ForestUnimodality.FlowComparisonCertificate
