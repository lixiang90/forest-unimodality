import ForestUnimodality.MessageSourceCellBounds
import ForestUnimodality.MessagePriceSpline

/-! A rationally checkable sufficient condition for the true logarithmic
penalty to be antitone. The square-root enclosure is proved in Lean. -/
namespace ForestUnimodality.MessagePriceSpline

structure LogMonotonicCertificate where
  logarithm : SourceLogWitness

def LogMonotonicCertificate.check (w : LogMonotonicCertificate) (P : Parameters) : Bool :=
  w.logarithm.check (5/(4*P.lower)) &&
    decide (0≤P.Dn+P.ell*((12:ℚ)/5-w.logarithm.hi))

theorem LogMonotonicCertificate.check_sound {w : LogMonotonicCertificate} {P : Parameters}
    (hP : P.check=true) (hw : w.check P=true) :
    0≤P.toReal.Dn+P.toReal.ell*
      (1+Real.sqrt 2-Real.log ((1+Real.sqrt 2)/(2*(P.lower:ℝ)))) := by
  have hp := Parameters.check_sound hP
  have hlower : 0<(P.lower:ℝ) := hp.1
  have hh : w.logarithm.check (5/(4*P.lower))=true ∧
      0≤P.Dn+P.ell*((12:ℚ)/5-w.logarithm.hi) := by
    simpa only [LogMonotonicCertificate.check,Bool.and_eq_true_iff,decide_eq_true_eq] using hw
  have hlog := (w.logarithm.certificate.check_sound hh.1).2
  push_cast at hlog
  have hs0 := Real.sqrt_nonneg (2:ℝ)
  have hsq := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hslo : (7:ℝ)/5≤Real.sqrt 2 := by nlinarith
  have hshi : Real.sqrt 2≤(3:ℝ)/2 := by nlinarith
  have ha : 0<(1+Real.sqrt 2)/(2*(P.lower:ℝ)) := by positivity
  have hab : (1+Real.sqrt 2)/(2*(P.lower:ℝ))≤5/(4*(P.lower:ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [hp.1]
  have hlog' := (Real.log_le_log ha hab).trans hlog
  have hbase : (12:ℝ)/5-(w.logarithm.hi:ℝ)≤
      1+Real.sqrt 2-Real.log ((1+Real.sqrt 2)/(2*(P.lower:ℝ))) := by linarith
  have hr : (0:ℝ)≤(P.Dn:ℝ)+(P.ell:ℝ)*((12:ℝ)/5-(w.logarithm.hi:ℝ)) := by
    have hr' : (0:ℝ)≤((P.Dn+P.ell*((12:ℚ)/5-w.logarithm.hi):ℚ):ℝ) := by
      exact_mod_cast hh.2
    simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_sub,Rat.cast_div,Rat.cast_ofNat] using hr'
  change 0≤(P.Dn:ℝ)+(P.ell:ℝ)*_
  exact hr.trans (add_le_add_right (mul_le_mul_of_nonneg_left hbase hp.2.2.2.2.2.1) _)

#print axioms LogMonotonicCertificate.check_sound
end ForestUnimodality.MessagePriceSpline
