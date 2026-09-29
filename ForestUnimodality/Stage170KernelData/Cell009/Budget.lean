import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell009.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell009
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(12031573700581518794799261047/100000000000000000000000000000)]
def R : ℚ := (653615921568627450980392156863/500000000000000000000000000000)
def D : ℚ := (76410016897506925207756232687/50000000000000000000000000000)
def vmax : ℚ := (969/4900)
def mlo : ℚ := (1059210526315789473684210526315781/10000000000000000000000000000000)
def mhi : ℚ := (24361842105263157894736842105262963/200000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (166282347150022147914148753852611014186298735446607798199005369894553974966762681373653992113/350000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (6898530571476645611994627/125000000000000000000000)) (.exp (-12743969511800161355017638345835424364033379282919686174682707/1000000000000000000000000000000000000000000000000000000000000) (729968924476712339/250000000000000000000000) (2919875697906849357/1000000000000000000000000) { parts := 13, inner := (-12743969511800161355017638345835424364033379282919686174682707/13000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (375196516204825329417693782787/1000000000000000000000000000000), innerHi := (93799129051206332354423445697/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (63246971764013881557200160259194685209633817827666673893999643130794330966259558927966079507277/140000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (6898530571476645611994627/125000000000000000000000)) (.exp (-293111298771403711165405681954214760372767723507152782017702261/20000000000000000000000000000000000000000000000000000000000000) (215843523693781867/500000000000000000000000) (86337409477512747/200000000000000000000000) { parts := 15, inner := (-293111298771403711165405681954214760372767723507152782017702261/300000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (94106136338698392773902791687/250000000000000000000000000000), innerHi := (376424545354793571095611166749/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell009
