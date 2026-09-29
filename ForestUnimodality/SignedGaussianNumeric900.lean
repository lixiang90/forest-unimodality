import ForestUnimodality.AnalyticNumericCertificate

namespace ForestUnimodality.SignedGaussianNumeric900
open AnalyticNumericCertificate

private def e000 : Expr := .rat 3
private def e001 : Expr := .sqrt e000 (4330127018922193 / 2500000000000000) (17320508075688773 / 10000000000000000)
private def e002 : Expr := .exp (14 / 15) (5085943275615909 / 2000000000000000) (12714858189039773 / 5000000000000000) { parts := 1, inner := (14 / 15), terms := 32, innerLo := (127148581890397726302007 / 50000000000000000000000), innerHi := (2542971637807954526040141 / 1000000000000000000000000) }
private def e003 : Expr := .rat (15 / 11)
private def e004 : Expr := .mul e003 e001
private def e005 : Expr := .sub e002 e004
private def e006 : Expr := .rat (4813 / 1000)
private def e007 : Expr := .rat (33 / 4)
private def e008 : Expr := .mul e007 e001
private def e009 : Expr := .exp (-4 / 3) (2635971381157267 / 10000000000000000) (658992845289317 / 2500000000000000) { parts := 2, inner := (-2 / 3), terms := 32, innerLo := (256708559516296013435993 / 500000000000000000000000), innerHi := (513417119032592026871987 / 1000000000000000000000000) }
private def e010 : Expr := .mul e008 e009
private def e011 : Expr := .sub e006 e010
private def e012 : Expr := .rat (39 / 25)
private def e013 : Expr := .exp (-2 / 5) (6703200460356393 / 10000000000000000) (3351600230178197 / 5000000000000000) { parts := 1, inner := (-2 / 5), terms := 32, innerLo := (41895002877227456296527 / 62500000000000000000000), innerHi := (670320046035639300744433 / 1000000000000000000000000) }
private def e014 : Expr := .mul e012 e013
private def e015 : Expr := .sub e011 e014

private theorem slope_check : e005.positiveCheck = true := by decide +kernel
private theorem curvature_check : e015.positiveCheck = true := by decide +kernel

theorem slope_margin : (0 : ℝ) < Real.exp (14 / 15) - (15 / 11) * Real.sqrt 3 := by
  have h := Expr.positiveCheck_sound e005 slope_check
  simpa [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, Expr.eval, neg_div] using h

theorem tight_curvature_margin : (0 : ℝ) < 4813 / 1000 - (33 / 4) * Real.sqrt 3 * Real.exp (-(4 / 3)) -
    (39 / 25) * Real.exp (-(2 / 5)) := by
  have h := Expr.positiveCheck_sound e015 curvature_check
  simpa [e000, e001, e002, e003, e004, e005, e006, e007, e008, e009, e010, e011, e012, e013, e014, e015, Expr.eval, neg_div] using h

theorem curvature_margin : (0 : ℝ) < 5 - (33 / 4) * Real.sqrt 3 * Real.exp (-(4 / 3)) -
    (39 / 25) * Real.exp (-(2 / 5)) := by linarith [tight_curvature_margin]

#print axioms slope_margin
#print axioms tight_curvature_margin
end ForestUnimodality.SignedGaussianNumeric900
