import ForestUnimodality.MessageSourceAssembly

/-! A tighter rational enclosure for the few signed-log sources whose
monotonicity margin needs more than the coarse square-root enclosure. -/
namespace ForestUnimodality.MessagePriceSpline

def sqrtTwoLo : ℚ := 1414213562373095048/1000000000000000000
def sqrtTwoHi : ℚ := 1414213562373095049/1000000000000000000

structure PreciseLogMonotonicCertificate where
  logarithm : SourceLogWitness

def PreciseLogMonotonicCertificate.check (w : PreciseLogMonotonicCertificate) (P : Parameters) : Bool :=
  w.logarithm.check ((1+sqrtTwoHi)/(2*P.lower)) &&
    decide (0≤P.Dn+P.ell*(1+sqrtTwoLo-w.logarithm.hi))

theorem PreciseLogMonotonicCertificate.check_sound
    {w : PreciseLogMonotonicCertificate} {P : Parameters} (hP : P.check=true)
    (hw : w.check P=true) :
    0≤P.toReal.Dn+P.toReal.ell*
      (1+Real.sqrt 2-Real.log ((1+Real.sqrt 2)/(2*(P.lower:ℝ)))) := by
  have hp := Parameters.check_sound hP
  have hlower : 0<(P.lower:ℝ) := hp.1
  have hh : w.logarithm.check ((1+sqrtTwoHi)/(2*P.lower))=true ∧
      0≤P.Dn+P.ell*(1+sqrtTwoLo-w.logarithm.hi) := by
    simpa only [PreciseLogMonotonicCertificate.check,Bool.and_eq_true_iff,decide_eq_true_eq] using hw
  have hlog := (w.logarithm.certificate.check_sound hh.1).2
  push_cast at hlog
  have hs0 := Real.sqrt_nonneg (2:ℝ)
  have hsq := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hslo : (sqrtTwoLo:ℝ)≤Real.sqrt 2 := by
    norm_num [sqrtTwoLo]
    nlinarith
  have hshi : Real.sqrt 2≤(sqrtTwoHi:ℝ) := by
    norm_num [sqrtTwoHi]
    nlinarith
  have ha : 0<(1+Real.sqrt 2)/(2*(P.lower:ℝ)) := by positivity
  have hab : (1+Real.sqrt 2)/(2*(P.lower:ℝ))≤
      (1+(sqrtTwoHi:ℝ))/(2*(P.lower:ℝ)) := by
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hlog' := (Real.log_le_log ha hab).trans hlog
  have hbase : 1+(sqrtTwoLo:ℝ)-(w.logarithm.hi:ℝ)≤
      1+Real.sqrt 2-Real.log ((1+Real.sqrt 2)/(2*(P.lower:ℝ))) := by linarith
  have hr : (0:ℝ)≤(P.Dn:ℝ)+(P.ell:ℝ)*(1+(sqrtTwoLo:ℝ)-(w.logarithm.hi:ℝ)) := by
    exact_mod_cast hh.2
  exact hr.trans (add_le_add_right (mul_le_mul_of_nonneg_left hbase hp.2.2.2.2.2.1) _)

end ForestUnimodality.MessagePriceSpline

namespace ForestUnimodality.MessageCells
open MessagePriceSpline

theorem sourceRowValid_of_precise (P : Parameters) (D : Domain)
    (mono : PreciseLogMonotonicCertificate) (cap : CapCertificate) (cells : List Cell)
    (hP : P.check=true) (hD : D.check=true) (hmono : mono.check P=true)
    (hcap : cap.check P D=true) (hcells : cells.all (fun c=>c.check P D)=true)
    (hcover : SourceIntervalCoverage.check Cell.left Cell.right 0
      (SelectionSource.probabilityCap D) cells=true) :
    MessageSourceRowValid P.toReal D.lower D.b := by
  intro p r z parentp hp hpq hr hr1 hparentLo hparentHi hend
  have hd := ParametricSource.Domain.check_sound hD
  have hq : (SelectionSource.probabilityCap D:ℝ)=(D.b:ℝ)/(1+(D.b:ℝ)) := by
    simp only [SelectionSource.probabilityCap,Rat.cast_div,Rat.cast_add,Rat.cast_one]
  by_cases he : p=(SelectionSource.probabilityCap D:ℝ)
  · have hz := hend (he.trans hq)
    subst p
    subst z
    exact CapCertificate.check_sound hcap hP hd hr hr1 hparentLo (by
      simpa only [capParent,Rat.cast_div,Rat.cast_mul,Rat.cast_sub,Rat.cast_one,Rat.cast_add]
        using hparentHi)
  · have hpq' : p<(D.b:ℝ)/(1+(D.b:ℝ)) :=
      lt_of_le_of_ne hpq (fun hh=>he (hh.trans hq.symm))
    obtain ⟨c,hc,hl,hu⟩ := SourceIntervalCoverage.check_sound Cell.left Cell.right hcover
      (p:=p) (by simpa only [Rat.cast_zero] using hp) (hq.symm ▸ hpq)
    exact Cell.check_sound ((List.all_eq_true.mp hcells) c hc) hP hd
      (PreciseLogMonotonicCertificate.check_sound hP hmono) hp hl hu hpq' hr hr1 hparentLo hparentHi

#print axioms MessagePriceSpline.PreciseLogMonotonicCertificate.check_sound
#print axioms sourceRowValid_of_precise
end ForestUnimodality.MessageCells
