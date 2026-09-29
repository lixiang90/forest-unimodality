import ForestUnimodality.LaplaceRateInterval
import ForestUnimodality.ExpEnclosure
import Mathlib.Tactic

/-! Rational certificates for the actual affine-source Chernoff exponent.
Only Taylor enclosures and rational inequalities are checked. In particular,
an upstream numerical evaluation of a logarithm is never a premise. -/
namespace ForestUnimodality.AffineTailRateCertificate

structure Certificate where
  uLower : ℚ
  uUpper : ℚ
  cLower : ℚ
  cUpper : ℚ
  logLower : ℚ
  logExpLower : ℚ
  logExpUpper : ℚ
  expU : ExpEnclosure.PowerCertificate
  expC : ExpEnclosure.PowerCertificate
  expLog : ExpEnclosure.PowerCertificate
  deriving Repr

def Certificate.rateLower (w : Certificate) (A C density alpha u q : ℚ) : ℚ :=
  q*((1-w.cUpper)/C)+alpha*w.logLower-
    A/C*(2*q/density-1)*(u-(1-w.cUpper)/C)

def Certificate.Accepts (w : Certificate) (A C density alpha u q rate : ℚ) : Prop :=
  0≤A ∧ 0<C ∧ 0<density ∧ 0≤alpha ∧ 0≤u ∧ 0≤q ∧ density≤2*q ∧
  w.expU.check (-u) w.uLower w.uUpper=true ∧
  w.expC.check (-C*u) w.cLower w.cUpper=true ∧
  w.expLog.check w.logLower w.logExpLower w.logExpUpper=true ∧
  w.logExpUpper≤1-q+q*w.uLower ∧ rate≤w.rateLower A C density alpha u q

instance (w : Certificate) (A C density alpha u q rate : ℚ) :
    Decidable (w.Accepts A C density alpha u q rate) := by
  unfold Certificate.Accepts
  infer_instance

def Certificate.check (w : Certificate) (A C density alpha u q rate : ℚ) : Bool :=
  decide (w.Accepts A C density alpha u q rate)

theorem Certificate.check_sound (w : Certificate) {A C density alpha u q rate : ℚ}
    (h : w.check A C density alpha u q rate=true) :
    (rate:ℝ)≤AffineLaplace.tailRate A C density alpha u q := by
  obtain ⟨hA,hC,hden,halpha,_,hq,hdenq,hu,hc,hl,hbase,hrate⟩ :=
    (of_decide_eq_true h : w.Accepts A C density alpha u q rate)
  have hA' : (0:ℝ)≤A := by exact_mod_cast hA
  have hC' : (0:ℝ)<C := by exact_mod_cast hC
  have hden' : (0:ℝ)<density := by exact_mod_cast hden
  have halpha' : (0:ℝ)≤alpha := by exact_mod_cast halpha
  have hq' : (0:ℝ)≤q := by exact_mod_cast hq
  have hdenq' : (density:ℝ)≤2*q := by exact_mod_cast hdenq
  have hu' := (w.expU.check_sound hu).1
  have hc' := (w.expC.check_sound hc).2
  have hl' := (w.expLog.check_sound hl).2
  have hbase' : (w.logExpUpper:ℝ)≤1-q+q*w.uLower := by exact_mod_cast hbase
  have hexp : Real.exp (w.logLower:ℝ)≤1-q+q*Real.exp (-(u:ℝ)) := by
    push_cast at hu'
    exact (hl'.trans hbase').trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hu' hq'))
  have hbasepos : 0<1-(q:ℝ)+q*Real.exp (-(u:ℝ)) := (Real.exp_pos _).trans_le hexp
  have hlog : (w.logLower:ℝ)≤Real.log (1-q+q*Real.exp (-(u:ℝ))) := by
    apply Real.exp_le_exp.mp
    rwa [Real.exp_log hbasepos]
  have hF : (1-(w.cUpper:ℝ))/C≤AffineLaplace.decayIntegral C u := by
    unfold AffineLaplace.decayIntegral
    push_cast at hc'
    exact div_le_div_of_nonneg_right (sub_le_sub_left hc' 1) hC'.le
  have hcoef : 0≤(A:ℝ)/C*(2*q/density-1) := by
    apply mul_nonneg (div_nonneg hA' hC'.le)
    have hh : (1:ℝ)≤2*q/density := (le_div_iff₀ hden').mpr (by simpa using hdenq')
    linarith
  have he : (w.rateLower A C density alpha u q:ℝ)=
      (q:ℝ)*((1-(w.cUpper:ℝ))/C)+alpha*w.logLower-
        A/C*(2*q/density-1)*(u-(1-w.cUpper)/C) := by
    simp [Certificate.rateLower]
  have hr : (rate:ℝ)≤w.rateLower A C density alpha u q := by exact_mod_cast hrate
  rw [he] at hr
  apply hr.trans
  unfold AffineLaplace.tailRate
  exact sub_le_sub (add_le_add (mul_le_mul_of_nonneg_left hF hq')
    (mul_le_mul_of_nonneg_left hlog halpha'))
    (mul_le_mul_of_nonneg_left (sub_le_sub_left hF (u:ℝ)) hcoef)

#print axioms Certificate.check_sound
end ForestUnimodality.AffineTailRateCertificate
