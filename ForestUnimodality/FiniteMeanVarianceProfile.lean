import ForestUnimodality.LogVarianceProfile

/-! Affine variance transfer with an explicit available-mean rectangle. -/
namespace ForestUnimodality

theorem bounded_mean_variance_profile {C D delta qa qb q alpha beta
    mlo mhi m n N variance : ℝ}
    (hq : q∈Set.Icc qa qb) (hm : m∈Set.Icc mlo mhi) (hm0 : 0≤m)
    (hN : n≤N) (hD : 0≤D)
    (ha : C*qa-qa*(1-qa)≤alpha+delta)
    (hb : C*qb-qb*(1-qb)≤alpha+delta)
    (hlo : delta*mlo+D*N≤beta) (hhi : delta*mhi+D*N≤beta)
    (hv : variance≤C*(q*m)+D*n) :
    variance≤(q*(1-q)+alpha)*m+beta := by
  have hc := mul_le_mul_of_nonneg_right (quadratic_profile_of_endpoints hq ha hb) hm0
  have hn := mul_le_mul_of_nonneg_left hN hD
  have hd : delta*m+D*N≤beta := by
    by_cases hs : 0≤delta
    · have hh := mul_le_mul_of_nonneg_left hm.2 hs
      linarith
    · have hh := mul_le_mul_of_nonpos_left hm.1 (le_of_not_ge hs)
      linarith
  nlinarith

#print axioms bounded_mean_variance_profile
end ForestUnimodality
