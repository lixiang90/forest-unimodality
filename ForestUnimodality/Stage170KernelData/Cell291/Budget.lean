import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell291.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell291
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(26642894181863998810416339533/250000000000000000000000000000)]
def R : ℚ := (1199131211/800000000)
def D : ℚ := (2379308466666666666666666666667/1000000000000000000000000000000)
def vmax : ℚ := (6/25)
def mlo : ℚ := (26434083731694228819476647646217739/400000000000000000000000000000000)
def mhi : ℚ := (607983925828967262847962895863007997/8000000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (5776894936586256781737281452687222485635459452332978633384174889502810534646234870801862156787/16000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (19776724523403949262956303/1000000000000000000000000)) (.exp (-704280495658061951184346602098833945976694235282322432671575887/100000000000000000000000000000000000000000000000000000000000000) (873672508657873937983/1000000000000000000000000) (13651132947779280281/15625000000000000000000) { parts := 8, inner := (-704280495658061951184346602098833945976694235282322432671575887/800000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (414637506166874461585624153477/1000000000000000000000000000000), innerHi := (207318753083437230792812076739/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (2238625362273652007096760070717755592133189619599244882703683718517957340417073359714466673036723/6400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (19776724523403949262956303/1000000000000000000000000)) (.exp (-16198451400135424877239971848273180757463967411493415951446245401/2000000000000000000000000000000000000000000000000000000000000000) (18985891214275200181/62500000000000000000000) (303774259428403202897/1000000000000000000000000) { parts := 9, inner := (-16198451400135424877239971848273180757463967411493415951446245401/18000000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (406604639785303140874323975873/1000000000000000000000000000000), innerHi := (203302319892651570437161987937/500000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck = true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mhi := by
  norm_num [budgetExpression_hi, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_hi_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mhi := by
  rw [← budgetExpression_hi_eval]
  exact budgetExpression_hi.positiveCheck_sound budgetExpression_hi_checked

theorem budget_positive {m : ℝ} (hm : m ∈ Set.Icc (mlo : ℝ) (mhi : ℝ)) :
    0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D m := by
  have hs := row.signCheck_sound row_checked
  have hdM : (0 : ℝ) ≤ row.dM := by norm_num [row]
  have hT : ∀ i ∈ row.terms, (0 : ℝ) ≤ row.price i := by
    intro i hi
    exact hs.price i hi
  exact KernelBudget.budget_pos_of_endpoints row.terms (∅ : Finset ℤ)
    row.A row.B row.dδ row.dM (R * vmax : ℚ) 0 D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ)) (fun _ => 0) (fun _ => 0)
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage170KernelData.Cell291
