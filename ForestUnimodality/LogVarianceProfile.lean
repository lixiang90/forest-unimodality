import ForestUnimodality.ElementaryEnclosure
import Mathlib.Tactic

/-! Convert a logarithmic forest variance bound to an affine profile on a
closed probability interval and a finite size interval. -/
namespace ForestUnimodality

theorem quadratic_profile_of_endpoints {C qa qb q alpha : ℝ}
    (hq : q ∈ Set.Icc qa qb)
    (ha : C*qa-qa*(1-qa)≤alpha) (hb : C*qb-qb*(1-qb)≤alpha) :
    C*q≤q*(1-q)+alpha := by
  have hprod := mul_nonneg (sub_nonneg.mpr hq.1) (sub_nonneg.mpr hq.2)
  by_cases hs : 0≤C-1+qa+qb
  · have hh := mul_nonneg hs (sub_nonneg.mpr hq.2)
    nlinarith
  · have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hs) (sub_nonneg.mpr hq.1)
    nlinarith

theorem log_variance_profile {C D ell a b lower qa qb q alpha beta g root
    logn logroot z nlo nhi n m variance : ℝ}
    (ha : 0<a) (hlower : 0<lower) (hb : 0<1+b) (haz : a≤z)
    (hell : 0≤ell) (hn : 0≤n) (hnlo : nlo≤n) (hnhi : n≤nhi) (hm : 0≤m)
    (hq : q ∈ Set.Icc qa qb)
    (hslo : C*qa-qa*(1-qa)≤alpha) (hshi : C*qb-qb*(1-qb)≤alpha)
    (hlogn : logn≤Real.log (a/lower))
    (hlogroot : logroot≤Real.log (1+a/(1+b)))
    (hg : D-ell*logn≤g) (hroot : root≤ell*logroot)
    (hbetalo : g*nlo-root≤beta) (hbetahi : g*nhi-root≤beta)
    (hvariance : variance≤C*(q*m)+(D-ell*Real.log (z/lower))*n-
      ell*Real.log (1+z/(1+b))) :
    variance≤(q*(1-q)+alpha)*m+beta := by
  have hln : logn≤Real.log (z/lower) := hlogn.trans
    (Real.log_le_log (div_pos ha hlower) (div_le_div_of_nonneg_right haz hlower.le))
  have hlr : logroot≤Real.log (1+z/(1+b)) := hlogroot.trans
    (Real.log_le_log (by positivity) (add_le_add_right
      (div_le_div_of_nonneg_right haz hb.le) 1))
  have hcoef : D-ell*Real.log (z/lower)≤g := by
    have hh := mul_le_mul_of_nonneg_left hln hell
    linarith
  have hr : root≤ell*Real.log (1+z/(1+b)) :=
    hroot.trans (mul_le_mul_of_nonneg_left hlr hell)
  have hres : g*n-root≤beta := by
    by_cases hg0 : 0≤g
    · have hh := mul_le_mul_of_nonneg_left hnhi hg0
      linarith
    · have hh := mul_le_mul_of_nonpos_left hnlo (le_of_not_ge hg0)
      linarith
  have hcn := mul_le_mul_of_nonneg_right hcoef hn
  have hs := mul_le_mul_of_nonneg_right (quadratic_profile_of_endpoints hq hslo hshi) hm
  nlinarith

#print axioms quadratic_profile_of_endpoints
#print axioms log_variance_profile
end ForestUnimodality
