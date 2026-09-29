import ForestUnimodality.MessageVarianceSource
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The complete-domain log-reference endpoint rule used by stage80.
The sufficient condition allows a negative Dn. -/
namespace ForestUnimodality

noncomputable def sourceLogPenalty (lower Dn ell p : ℝ) : ℝ :=
  (Dn-ell*sourceLogReference lower p)/p

theorem sourceLogReference_minimum {lower p : ℝ}
    (hlower : 0<lower) (hp : 0<p) (hp1 : p<1) :
    1+Real.sqrt 2-Real.log ((1+Real.sqrt 2)/(2*lower)) ≤
      (1+p)/(1-p)-sourceLogReference lower p := by
  let q : ℝ := Real.sqrt 2
  let c : ℝ := q/2
  let t : ℝ := p/(1-p)
  have hq : 0<q := Real.sqrt_pos.mpr (by norm_num)
  have hq2 : q^2=2 := Real.sq_sqrt (by norm_num)
  have hc : 0<c := by dsimp [c]; positivity
  have hc1 : 0<1+c := by linarith
  have hp' : 0<1-p := sub_pos.mpr hp1
  have ht : 0<t := div_pos hp hp'
  have ht1 : 0<1+t := by linarith
  have hl1 := Real.log_le_sub_one_of_pos (div_pos ht hc)
  have hl2 := Real.log_le_sub_one_of_pos (div_pos ht1 hc1)
  rw [Real.log_div ht.ne' hc.ne'] at hl1
  rw [Real.log_div ht1.ne' hc1.ne'] at hl2
  have hslope : (t/c-1)+((1+t)/(1+c)-1)=2*(t-c) := by
    field_simp [hc.ne',hc1.ne']
    dsimp [c]
    nlinarith [congrArg (fun x:ℝ=>x*t) hq2,congrArg (fun x:ℝ=>x*q) hq2]
  have hcprod : c*(1+c)=(1+q)/2 := by dsimp [c]; nlinarith [hq2]
  have hconst : Real.log c+Real.log (1+c)-Real.log lower=
      Real.log ((1+q)/(2*lower)) := by
    rw [←Real.log_mul hc.ne' hc1.ne',hcprod]
    rw [show (1+q)/(2*lower)=((1+q)/2)/lower by ring]
    rw [Real.log_div (by positivity) hlower.ne']
  have htden : 1+t=1/(1-p) := by dsimp [t]; field_simp; ring
  have hG : sourceLogReference lower p=Real.log t+Real.log (1+t)-Real.log lower := by
    unfold sourceLogReference
    rw [htden,Real.log_div one_ne_zero hp'.ne']
    dsimp [t]
    rw [Real.log_div hp.ne' hp'.ne']
    simp only [Real.log_one,zero_sub]
    ring
  have hratio : (1+p)/(1-p)=1+2*t := by dsimp [t]; field_simp; ring
  change 1+q-Real.log ((1+q)/(2*lower))≤_
  rw [hG,hratio,←hconst]
  have hsum := add_le_add hl1 hl2
  rw [hslope] at hsum
  dsimp [c] at hsum
  linarith

theorem hasDerivAt_sourceLogPenalty {lower Dn ell p : ℝ}
    (hp : 0<p) (hp1 : p<1) :
    HasDerivAt (sourceLogPenalty lower Dn ell)
      (-(Dn+ell*((1+p)/(1-p)-sourceLogReference lower p))/p^2) p := by
  have hp' : 1-p≠0 := (sub_pos.mpr hp1).ne'
  have hl : HasDerivAt (fun x:ℝ=>Real.log (1-x)) (-1/(1-p)) p := by
    simpa using ((hasDerivAt_id p).const_sub 1).log hp'
  have hg : HasDerivAt (sourceLogReference lower) (1/p+2/(1-p)) p := by
    convert (((hasDerivAt_id p).log hp.ne').sub (hl.const_mul 2)).sub_const (Real.log lower) using 1
    all_goals first | rfl | (dsimp only [sourceLogReference,id_eq,Pi.sub_apply]; ring)
  convert ((hg.const_mul ell).const_sub Dn).div (hasDerivAt_id p) hp.ne' using 1
  all_goals first | rfl |
    (dsimp only [sourceLogPenalty,id_eq,Pi.div_apply]; field_simp [hp.ne',hp']; ring)

theorem sourceLogPenalty_antitone {lower Dn ell : ℝ}
    (hlower : 0<lower) (hell : 0≤ell)
    (hprice : 0≤Dn+ell*(1+Real.sqrt 2-Real.log ((1+Real.sqrt 2)/(2*lower)))) :
    AntitoneOn (sourceLogPenalty lower Dn ell) (Set.Ioo (0:ℝ) 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 1)
  · intro p hp
    exact (hasDerivAt_sourceLogPenalty hp.1 hp.2).continuousAt.continuousWithinAt
  · intro p hp
    have hh : p∈Set.Ioo (0:ℝ) 1 := interior_subset hp
    exact (hasDerivAt_sourceLogPenalty hh.1 hh.2).differentiableAt.differentiableWithinAt
  · intro p hp
    have hh : p∈Set.Ioo (0:ℝ) 1 := interior_subset hp
    rw [(hasDerivAt_sourceLogPenalty (lower:=lower) (Dn:=Dn) (ell:=ell) hh.1 hh.2).deriv]
    have hmin := mul_le_mul_of_nonneg_left (sourceLogReference_minimum hlower hh.1 hh.2) hell
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    linarith

#print axioms sourceLogReference_minimum
#print axioms sourceLogPenalty_antitone
end ForestUnimodality
