import ForestUnimodality.SourceGeneralCells
import ForestUnimodality.SourceGeneralEndpoints
import ForestUnimodality.SourceIntervalCoverage

/-! Exhaustive assembly of the analytically certified origin, the finite
real interval chain, and the true leaf endpoint. -/
namespace ForestUnimodality.ParametricSource

theorem sourceRowValid_of_checked (P : RationalSourceParameters) (D : Domain)
    (origin : Origin) (leaf : Leaf) (cells : List Cell)
    (hP : P.admissibleCheck=true) (hD : D.check=true)
    (ho : origin.check P D=true) (hl : leaf.check P D=true)
    (hc : cells.all (Cell.check P D)=true)
    (hcoverage : SourceIntervalCoverage.check Cell.left Cell.right origin.delta (D.b/(1+D.b)) cells=true) :
    SourceRowValid P.toReal D.lower D.b := by
  have hPr := P.admissible_sound hP
  have hDr := Domain.check_sound hD
  intro a parentA hs p r z hp hpq hr hr1 hend
  by_cases he : p=(D.b:ℝ)/(1+(D.b:ℝ))
  · subst p
    have hz : z=a := hend rfl
    subst z
    exact Leaf.check_sound hl hPr hDr hs hr hr1
  have hpq' : p<(D.b:ℝ)/(1+(D.b:ℝ)) := lt_of_le_of_ne hpq he
  by_cases hpo : p≤(origin.delta:ℝ)
  · exact Origin.check_sound ho hPr hDr hs hp hpo hr hr1
  have hUpper : p≤((D.b/(1+D.b):ℚ):ℝ) := by
    push_cast
    exact hpq
  obtain ⟨c,hmem,hcl,hcr⟩ := SourceIntervalCoverage.check_sound Cell.left Cell.right hcoverage
    (lt_of_not_ge hpo) hUpper
  exact Cell.check_sound P D hDr hP ((List.all_eq_true.mp hc) c hmem) hs hcl hcr hpq' hr hr1

#print axioms sourceRowValid_of_checked
end ForestUnimodality.ParametricSource
