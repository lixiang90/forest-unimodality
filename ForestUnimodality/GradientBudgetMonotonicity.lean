import ForestUnimodality.UnboundedBudget
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The shifted square-root exponential charge in stage900 (9.5) is a
difference of two positive monomials. Its monotonicity is proved for that
complete expression, rather than inferred separately from the monomials. -/
namespace ForestUnimodality.GradientBudgetMonotonicity
open Set

noncomputable def shiftedCost (A rate m : ℝ) : ℝ :=
  (m-A)/Real.sqrt m*Real.exp (-rate*m)

theorem threshold_propagates {A rate start m : ℝ}
    (hA : 0≤A) (hstart : A<start) (hr : 0≤rate) (hm : start≤m)
    (hthreshold : start+A≤2*rate*start*(start-A)) :
    m+A≤2*rate*m*(m-A) := by
  have hs : 0<start := hA.trans_lt hstart
  have hm0 : 0<m := hs.trans_le hm
  have hbase : 1≤2*rate*(start-A) := by
    apply (mul_le_mul_iff_right₀ hs).mp
    nlinarith only [hthreshold,hA]
  have hcoeff : 0≤2*rate*(m+start-A)-1 := by
    nlinarith only [hbase,mul_nonneg hr hm0.le]
  have hprod := mul_nonneg (sub_nonneg.mpr hm) hcoeff
  nlinarith only [hprod,hthreshold]

theorem hasDerivAt_shiftedCost (A rate : ℝ) {m : ℝ} (hm : 0<m) :
    HasDerivAt (shiftedCost A rate)
      (Real.exp (-rate*m)/(2*m*Real.sqrt m)*(m+A-2*rate*m*(m-A))) m := by
  have hsq : 0<Real.sqrt m := Real.sqrt_pos.mpr hm
  have hd := (((hasDerivAt_id m).sub_const A).div
    (Real.hasDerivAt_sqrt hm.ne') hsq.ne').mul
    (((hasDerivAt_id m).const_mul (-rate)).exp)
  apply hd.congr_deriv
  simp only [id_eq,mul_one,one_mul,Pi.div_apply]
  field_simp
  ring_nf
  simp only [Real.sq_sqrt hm.le]
  ring

/-- A single exact endpoint condition controls the whole real half-line. -/
theorem shiftedCost_antitoneOn {A rate start : ℝ}
    (hA : 0≤A) (hstart : A<start) (hr : 0≤rate)
    (hthreshold : start+A≤2*rate*start*(start-A)) :
    AntitoneOn (shiftedCost A rate) (Ici start) := by
  have hs : 0<start := hA.trans_lt hstart
  have hd (m : ℝ) (hm : m∈Ici start) := hasDerivAt_shiftedCost A rate (hs.trans_le hm)
  apply antitoneOn_of_deriv_nonpos (convex_Ici start)
  · intro m hm; exact (hd m hm).continuousAt.continuousWithinAt
  · intro m hm; exact (hd m (interior_subset hm)).differentiableAt.differentiableWithinAt
  · intro m hm
    have hms : start≤m := interior_subset hm
    have hm0 : 0<m := hs.trans_le hms
    rw [(hd m hms).deriv]
    apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
    linarith [threshold_propagates hA hstart hr hms hthreshold]

theorem shiftedCost_le_start {A rate start m : ℝ}
    (hA : 0≤A) (hstart : A<start) (hr : 0≤rate)
    (hthreshold : start+A≤2*rate*start*(start-A)) (hm : start≤m) :
    shiftedCost A rate m≤shiftedCost A rate start :=
  shiftedCost_antitoneOn hA hstart hr hthreshold (by simp) hm hm


/-- Write C=c0/v and A_i=c_i/(v*alpha_i) to obtain exactly (9.5). -/
noncomputable def gradientCost (C D a A0 A1 rate0 rate1 m : ℝ) : ℝ :=
  C/Real.sqrt m*(1+D/(a*m))+(A1-A0)/Real.sqrt m*Real.exp (-rate0*m)+
    shiftedCost A1 rate1 m

theorem gradientCost_antitoneOn {C D a A0 A1 rate0 rate1 start : ℝ}
    (hC : 0≤C) (hD : 0≤D) (ha : 0<a) (hA : A0≤A1)
    (hA1 : 0≤A1) (hstart : A1<start) (hr0 : 0≤rate0) (hr1 : 0≤rate1)
    (hthreshold : start+A1≤2*rate1*start*(start-A1)) :
    AntitoneOn (gradientCost C D a A0 A1 rate0 rate1) (Ici start) := by
  intro x hx y hy hxy
  have hx0 : 0<x := (hA1.trans_lt hstart).trans_le hx
  have hy0 : 0<y := hx0.trans_le hxy
  have hsqx : 0<Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hsqy : 0<Real.sqrt y := Real.sqrt_pos.mpr hy0
  have hsq := Real.sqrt_le_sqrt hxy
  have hf : C/Real.sqrt y≤C/Real.sqrt x := div_le_div_of_nonneg_left hC hsqx hsq
  have hJ : 1+D/(a*y)≤1+D/(a*x) :=
    add_le_add le_rfl (div_le_div_of_nonneg_left hD (by positivity)
      (mul_le_mul_of_nonneg_left hxy ha.le))
  have hmain := mul_le_mul hf hJ (by positivity : 0≤1+D/(a*y))
    (div_nonneg hC hsqx.le)
  have hfrac : (A1-A0)/Real.sqrt y≤(A1-A0)/Real.sqrt x :=
    div_le_div_of_nonneg_left (sub_nonneg.mpr hA) hsqx hsq
  have he : Real.exp (-rate0*y)≤Real.exp (-rate0*x) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hxy hr0])
  have hmiddle := mul_le_mul hfrac he (Real.exp_pos _).le
    (div_nonneg (sub_nonneg.mpr hA) hsqx.le)
  have hlast := shiftedCost_antitoneOn hA1 hstart hr1 hthreshold hx hy hxy
  exact add_le_add (add_le_add hmain hmiddle) hlast

theorem gradientCost_le_start {C D a A0 A1 rate0 rate1 start m : ℝ}
    (hC : 0≤C) (hD : 0≤D) (ha : 0<a) (hA : A0≤A1)
    (hA1 : 0≤A1) (hstart : A1<start) (hr0 : 0≤rate0) (hr1 : 0≤rate1)
    (hthreshold : start+A1≤2*rate1*start*(start-A1)) (hm : start≤m) :
    gradientCost C D a A0 A1 rate0 rate1 m≤gradientCost C D a A0 A1 rate0 rate1 start :=
  gradientCost_antitoneOn hC hD ha hA hA1 hstart hr0 hr1 hthreshold (by simp) hm hm

#print axioms threshold_propagates
#print axioms hasDerivAt_shiftedCost
#print axioms shiftedCost_antitoneOn
#print axioms gradientCost_antitoneOn
end ForestUnimodality.GradientBudgetMonotonicity
