import ForestUnimodality.BernoulliCutoff
import ForestUnimodality.LogisticTilt

/-! Endpoint conditions imply the smoothing hypotheses throughout a real
activity interval, including intervals crossing activity one. -/
namespace ForestUnimodality.SmoothingInterval

theorem activity_fraction_monotone {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    a / (1 + a) ≤ b / (1 + b) := by
  apply (div_le_div_iff₀ (by positivity : 0 < 1 + a)
    (by linarith : 0 < 1 + b)).mpr
  nlinarith

theorem activity_fraction_bounds {a z b : ℝ} (ha : 0 ≤ a) (haz : a ≤ z) (hzb : z ≤ b) :
    a / (1 + a) ≤ z / (1 + z) ∧ z / (1 + z) ≤ b / (1 + b) :=
  ⟨activity_fraction_monotone ha haz, activity_fraction_monotone (ha.trans haz) hzb⟩

theorem variance_le_quarter (q : ℝ) : q * (1 - q) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (q - 1 / 2)]

theorem variance_le_right {q hi : ℝ} (hq : q ≤ hi) (hhi : hi ≤ 1 / 2) :
    q * (1 - q) ≤ hi * (1 - hi) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hq) (show 0 ≤ 1 - hi - q by linarith)]

theorem variance_le_left {lo q : ℝ} (hq : lo ≤ q) (hlo : 1 / 2 ≤ lo) :
    q * (1 - q) ≤ lo * (1 - lo) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hq) (show 0 ≤ q + lo - 1 by linarith)]

theorem variance_le_interval_max {lo hi q V : ℝ} (hlo : lo ≤ q) (hhi : q ≤ hi)
    (hleft : hi ≤ 1 / 2 → hi * (1 - hi) ≤ V)
    (hright : 1 / 2 ≤ lo → lo * (1 - lo) ≤ V)
    (hcenter : lo < 1 / 2 → 1 / 2 < hi → 1 / 4 ≤ V) : q * (1 - q) ≤ V := by
  by_cases hh : hi ≤ 1 / 2
  · exact (variance_le_right hhi hh).trans (hleft hh)
  by_cases hl : 1 / 2 ≤ lo
  · exact (variance_le_left hlo hl).trans (hright hl)
  exact (variance_le_quarter q).trans (hcenter (lt_of_not_ge hl) (lt_of_not_ge hh))

theorem asymmetry_le_endpoints {lo hi q eta : ℝ} (hlo : lo ≤ q) (hhi : q ≤ hi)
    (hel : |1 - 2 * lo| ≤ eta) (heh : |1 - 2 * hi| ≤ eta) : |1 - 2 * q| ≤ eta := by
  obtain ⟨hl1, hl2⟩ := abs_le.mp hel
  obtain ⟨hh1, hh2⟩ := abs_le.mp heh
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem cutoff_of_variance_lower {q v T : ℝ} (hv : (1 / 6 : ℝ) ≤ v)
    (hvq : v ≤ q * (1 - q)) (hT : 0 < T) (hTp : T < Real.pi)
    (hdamp : (1 / 6 : ℝ) ≤ v * (1 - T ^ 2 / 12))
    (hquartic : 1 - 5 * v - 10 * v ^ 2 + (15 / 512 : ℝ) * T ^ 2 ≤ 0) :
    BernoulliCutoff.Valid q T := by
  have hv0 : 0 ≤ v := by linarith
  have hq0 : 0 ≤ q * (1 - q) := hv0.trans hvq
  have hq1 := variance_le_quarter q
  have hfac : 0 ≤ 1 - T ^ 2 / 12 := by
    by_contra hh
    have he := mul_nonpos_of_nonneg_of_nonpos hv0 (le_of_lt (lt_of_not_ge hh))
    linarith
  have hd := mul_le_mul_of_nonneg_right hvq hfac
  have hsq := pow_le_pow_left₀ hv0 hvq 2
  have hcube := pow_le_pow_left₀ hq0 hq1 3
  have hcubeCost := mul_le_mul_of_nonneg_right hcube
    (show 0 ≤ (15 / 8 : ℝ) * T ^ 2 by positivity)
  refine ⟨hT, hTp, hv.trans hvq, hdamp.trans hd, ?_⟩
  norm_num at hcubeCost
  nlinarith

theorem cutoff_of_endpoints {lo hi q v T : ℝ} (hlo : lo ≤ q) (hhi : q ≤ hi)
    (hvlo : v ≤ lo * (1 - lo)) (hvhi : v ≤ hi * (1 - hi))
    (hv : (1 / 6 : ℝ) ≤ v) (hT : 0 < T) (hTp : T < Real.pi)
    (hdamp : (1 / 6 : ℝ) ≤ v * (1 - T ^ 2 / 12))
    (hquartic : 1 - 5 * v - 10 * v ^ 2 + (15 / 512 : ℝ) * T ^ 2 ≤ 0) :
    BernoulliCutoff.Valid q T :=
  cutoff_of_variance_lower hv
    ((le_min hvlo hvhi).trans (bernoulli_variance_ge_min hlo hhi)) hT hTp hdamp hquartic

#print axioms variance_le_interval_max
#print axioms cutoff_of_endpoints
end ForestUnimodality.SmoothingInterval
