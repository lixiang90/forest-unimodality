import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell421.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell421
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(115176453448796176308624641393/1000000000000000000000000000000)]
def R : ℚ := (950083027272727272727272727273/500000000000000000000000000000)
def D : ℚ := (1427449926666666666666666666667/500000000000000000000000000000)
def vmax : ℚ := (45/196)
def mlo : ℚ := (43340955008520809526966994918853/1000000000000000000000000000000)
def mhi : ℚ := (3009788542258389550483819091587/62500000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (74251993341422544872292830222910554970793804060245389540327671833553471231878681541217441/245000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (10034596400621328626812101/1000000000000000000000000)) (.exp (-4991857486965266503392939752084549665839903475905860259882229/1000000000000000000000000000000000000000000000000000000000000) (3396517396264422432731/500000000000000000000000) (6793034792528844865463/1000000000000000000000000) { parts := 5, inner := (-4991857486965266503392939752084549665839903475905860259882229/5000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (368479021877295021905184169427/1000000000000000000000000000000), innerHi := (92119755469323755476296042357/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (1259558892430217483239138067086371825017102939851841076858403752156435143671012916947367/4375000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (10034596400621328626812101/1000000000000000000000000)) (.exp (-346656769928143507180065260561425460454806508102124898260691/62500000000000000000000000000000000000000000000000000000000) (780210945976415913753/200000000000000000000000) (1950527364941039784383/500000000000000000000000) { parts := 6, inner := (-346656769928143507180065260561425460454806508102124898260691/375000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (396762246446651943870791241303/1000000000000000000000000000000), innerHi := (49595280805831492983848905163/125000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell421
