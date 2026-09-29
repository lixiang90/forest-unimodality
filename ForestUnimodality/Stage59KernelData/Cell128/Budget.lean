import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell128.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell128
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(48915218497521997821096372393/500000000000000000000000000000)]
def alpha : ℚ := (171050057523414661858615800779/1000000000000000000000000000000)
def D : ℚ := (293408401563805020007275372863/200000000000000000000000000000)
def mlo : ℚ := (2057824635508924921651451151383/125000000000000000000000000000)
def mhi : ℚ := (21788731434800381523368306308761/1000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (63604999910230192437078617882465760508455331834396476681346161747240316966600270239083/125000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (2383714008525550376305091/1000000000000000000000000)) (.exp (-100658941675502627312083434666674669821417754995824384969519/62500000000000000000000000000000000000000000000000000000000) (199779091216849847230163/1000000000000000000000000) (49944772804212461807541/250000000000000000000000) { parts := 2, inner := (-100658941675502627312083434666674669821417754995824384969519/125000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (446966543733252866414773381001/1000000000000000000000000000000), innerHi := (223483271866626433207386690501/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (19715294417758621618378966038551152650853458011513700548903632931214390893088324344399/62500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (2383714008525550376305091/1000000000000000000000000)) (.exp (-1065800558917086642127942249411840813070570784309113294435073/500000000000000000000000000000000000000000000000000000000000) (4745886943397950903001/40000000000000000000000) (59323586792474386287513/500000000000000000000000) { parts := 3, inner := (-355266852972362214042647416470613604356856928103037764811691/500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (491381874038102753855827764349/1000000000000000000000000000000), innerHi := (9827637480762055077116555287/20000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck=true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval = budget mhi := by
  norm_num [budgetExpression_hi, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_hi_positive : 0 < budget mhi := by
  rw [← budgetExpression_hi_eval]
  exact budgetExpression_hi.positiveCheck_sound budgetExpression_hi_checked

theorem budget_positive {m : ℝ} (hm : m ∈ Set.Icc (mlo : ℝ) (mhi : ℝ)) :
    0 < budget m := by
  have hs := row.signCheck_sound row_checked
  have hdM : (0 : ℝ) ≤ row.dM := by norm_num [row]
  have hT : ∀ i ∈ row.terms, (0 : ℝ) ≤ row.price i := by
    intro i hi
    exact hs.price i hi
  exact KernelBudget.budget_pos_of_endpoints row.terms row.fixedIndices
    row.A row.B row.dδ row.dM alpha varianceIntercept D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ))
    (fun j => (row.fixedPrice j : ℝ)) (fun j => (countBound j : ℝ))
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage59KernelData.Cell128
