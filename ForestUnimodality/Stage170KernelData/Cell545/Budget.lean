import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell545.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell545
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(107754504643767711713070558667/1000000000000000000000000000000)]
def R : ℚ := (614337511/400000000)
def D : ℚ := (2365851798699186991869918699187/1000000000000000000000000000000)
def vmax : ℚ := (9840/41209)
def mlo : ℚ := (42282647772660323435816934804827/1000000000000000000000000000000)
def mhi : ℚ := (447698623475226954026296956757/10000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (21770335587708049033678982239158713762661031567675176269246983708455376535265188458521757469/64389062500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (14549398546254641573227673/1000000000000000000000000)) (.exp (-4556145765769921314081325712660873766350604159814505498285609/1000000000000000000000000000000000000000000000000000000000000) (328201874269771970779/31250000000000000000000) (10502459976632703064929/1000000000000000000000000) { parts := 5, inner := (-4556145765769921314081325712660873766350604159814505498285609/5000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (402029764059881321985746220531/1000000000000000000000000000000), innerHi := (100507441014970330496436555133/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (422788899833612802449737371196012584348431492245932831508450874821209642655666573799371539/1287781250000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (14549398546254641573227673/1000000000000000000000000)) (.exp (-48241543402269755090272860486998374327868169190955930562919/10000000000000000000000000000000000000000000000000000000000) (8033344474985243773147/1000000000000000000000000) (2008336118746310943287/250000000000000000000000) { parts := 5, inner := (-48241543402269755090272860486998374327868169190955930562919/50000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (381047641622017947022503761843/1000000000000000000000000000000), innerHi := (95261910405504486755625940461/250000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell545
