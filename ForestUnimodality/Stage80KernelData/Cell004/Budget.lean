import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage80KernelData.Cell004.Parameters

namespace ForestUnimodality.Stage80KernelData.Cell004
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(179929245891556516040624553247/1000000000000000000000000000000)]
def R : ℚ := (8458603/6250000)
def D : ℚ := (63356039/40000000)
def vmax : ℚ := (10/49)
def mlo : ℚ := (35/1)
def mhi : ℚ := (175/4)
def alpha : ℚ := (8458603/30625000)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.rat (33971864752976319674128520416313591/80000000000000000000000000000000000)) (.mul (.rat (354192291695511127236351/78125000000000000000000)) (.exp (-1259504721240895612284371872729/200000000000000000000000000000) (1840857826029769264091/1000000000000000000000000) (460214456507442316023/250000000000000000000000) { parts := 7, inner := (-179929245891556516040624553247/200000000000000000000000000000), terms := 40, innerLo := (406713517554402731033784261719/1000000000000000000000000000000), innerHi := (10167837938860068275844606543/25000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (26292787391117303836290840206313591/64000000000000000000000000000000000)) (.mul (.rat (354192291695511127236351/78125000000000000000000)) (.exp (-1259504721240895612284371872729/160000000000000000000000000000) (190653733601312544607/500000000000000000000000) (76261493440525017843/200000000000000000000000) { parts := 8, inner := (-1259504721240895612284371872729/1280000000000000000000000000000), terms := 40, innerLo := (23363582187539777329275044877/62500000000000000000000000000), innerHi := (373817315000636437268400718033/1000000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck = true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mhi := by
  norm_num [budgetExpression_hi, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]

theorem budget_hi_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mhi := by
  rw [← budgetExpression_hi_eval]
  exact budgetExpression_hi.positiveCheck_sound budgetExpression_hi_checked

theorem budget_positive {m : ℝ} (hm : m ∈ Set.Icc (mlo : ℝ) (mhi : ℝ)) :
    0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D m := by
  have hs := row.signCheck_sound row_checked
  have hdM : (0 : ℝ) ≤ row.dM := by norm_num [row]
  have hT : ∀ i ∈ row.terms, (0 : ℝ) ≤ row.price i := by
    intro i hi
    exact hs.price i hi
  exact KernelBudget.budget_pos_of_endpoints row.terms (∅ : Finset ℤ)
    row.A row.B row.dδ row.dM alpha varianceIntercept D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ)) (fun _ => 0) (fun _ => 0)
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage80KernelData.Cell004
