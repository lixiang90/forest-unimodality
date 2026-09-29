import ForestUnimodality.MessageCapCertificate
import ForestUnimodality.MessageLogBonus

/-! Complete finite-to-continuous assembly for spline, signed-response-flow,
and signed-log message sources. Every probability, response, retention and
same-parent price is covered by checked rational certificates. -/
namespace ForestUnimodality.MessageCells
open MessagePriceSpline

def Cell.left (c : Cell) : ℚ := c.bounds.base.left
def Cell.right (c : Cell) : ℚ := c.bounds.base.right

theorem sourceRowValid_of_checked (P : Parameters) (D : Domain)
    (mono : LogMonotonicCertificate) (cap : CapCertificate) (cells : List Cell)
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
      (LogMonotonicCertificate.check_sound hP hmono) hp hl hu hpq' hr hr1 hparentLo hparentHi

#print axioms sourceRowValid_of_checked
end ForestUnimodality.MessageCells
