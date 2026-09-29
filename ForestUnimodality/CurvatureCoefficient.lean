import ForestUnimodality.AnalyticKernelSign

/-! Positive arithmetic curvature of tilted probabilities implies strict
log-concavity of the original coefficients; the activity weights cancel. -/
namespace ForestUnimodality

theorem coefficient_strict_logConcavity_of_tiltedCenter (c : ℕ→ℕ)
    {z Z : ℝ} (hz : 0<z) (hZ : 0<Z) {k : ℕ} (hk : 1≤k)
    (h : 0<tiltedCenter c z Z k) : c (k-1)*c (k+1)<c k^2 := by
  have hf : 0<z^(k-1)/Z := by positivity
  have he : tiltedCenter c z Z k=(z^(k-1)/Z)*
      (2*z*(c k:ℝ)-(c (k-1):ℝ)-z^2*(c (k+1):ℝ)) := by
    rw [tiltedCenter_eq c z Z hk]
    ring
  rw [he] at h
  have hpos:=pos_of_mul_pos_right h hf.le
  have hcn : 0≤(c (k-1):ℝ)+z^2*(c (k+1):ℝ) := by positivity
  have hsum : 0<2*z*(c k:ℝ)+(c (k-1):ℝ)+z^2*(c (k+1):ℝ) := by linarith
  have hm:=mul_pos hpos hsum
  have hgap : 0<z^2*((c k:ℝ)^2-(c (k-1):ℝ)*(c (k+1):ℝ)) := by
    nlinarith only [hm,sq_nonneg ((c (k-1):ℝ)-z^2*(c (k+1):ℝ))]
  have hr : (c (k-1):ℝ)*(c (k+1):ℝ)<(c k:ℝ)^2 := by
    have := pos_of_mul_pos_right hgap (sq_nonneg z)
    linarith
  exact_mod_cast hr

#print axioms coefficient_strict_logConcavity_of_tiltedCenter
end ForestUnimodality
