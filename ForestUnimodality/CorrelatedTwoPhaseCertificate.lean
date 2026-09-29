import ForestUnimodality.CorrelatedTwoPhase

namespace ForestUnimodality.CorrelatedTwoPhase

theorem endpoint_sound (first second : FlowComparisonCertificate.Certificate)
    {A C₁ C₂ rho u v q r : ℚ}
    (hfirst : first.check q (A*(2*q/rho-1)) C₁ u=true)
    (hsecond : second.check (first.endBound q) 0 C₂ (v-u)=true)
    (hr : r≤first.areaBound q u+second.areaBound (first.endBound q) (v-u)) :
    (r:ℝ)≤rate A C₁ C₂ rho u v q := by
  have h₁ := first.check_sound hfirst
  have h₂ := second.check_sound hsecond
  have hs : second.Accepts (first.endBound q) 0 C₂ (v-u) := of_decide_eq_true hsecond
  have hC : (0:ℝ)<C₂ := by exact_mod_cast hs.2.2.1
  have ht : (0:ℝ)≤(v:ℝ)-u := by exact_mod_cast hs.2.2.2.1
  have hm := mul_le_mul_of_nonneg_right h₁.1
    (PiecewiseFlowLaplace.decayIntegral_nonneg hC ht)
  have hi : PiecewiseFlowLaplace.integralLower (first.endBound q) 0 C₂ ((v:ℝ)-u)≤
      PiecewiseFlowLaplace.integralLower
        (PiecewiseFlowLaplace.endLower q (A*(2*q/rho-1):ℚ) C₁ u) 0 C₂ ((v:ℝ)-u) := by
    simpa only [PiecewiseFlowLaplace.integralLower,zero_div,zero_mul,sub_zero] using hm
  have hr' : (r:ℝ)≤(first.areaBound q u:ℝ)+(second.areaBound (first.endBound q) (v-u):ℝ) :=
    by exact_mod_cast hr
  have h₂' : (second.areaBound (first.endBound q) (v-u):ℝ)≤
      PiecewiseFlowLaplace.integralLower (first.endBound q) 0 C₂ ((v:ℝ)-u) := by
    simpa only [Rat.cast_zero,Rat.cast_sub] using h₂.2
  have hh := hr'.trans (add_le_add h₁.2 (h₂'.trans hi))
  simpa only [rate,Rat.cast_mul,Rat.cast_sub,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using hh

#print axioms endpoint_sound
end ForestUnimodality.CorrelatedTwoPhase
