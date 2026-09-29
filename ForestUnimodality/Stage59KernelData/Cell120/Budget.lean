import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell120.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell120
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(19550203102286092436543069687/200000000000000000000000000000)]
def alpha : ℚ := (175518861278118533782097411073/1000000000000000000000000000000)
def D : ℚ := (1478350685283404571640958929567/1000000000000000000000000000000)
def mlo : ℚ := (3311430425512190599796050801891/200000000000000000000000000000)
def mhi : ℚ := (43827755631778993232594790025029/2000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (1059516639380333244647810167480250445452021571092721932770120019634943649350293567174391/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (5244934506623327941099433/1000000000000000000000000)) (.exp (-64739137377852983801825629595576151106690333169295044378117/40000000000000000000000000000000000000000000000000000000000) (99100022063619007939627/500000000000000000000000) (39640008825447603175851/200000000000000000000000) { parts := 2, inner := (-64739137377852983801825629595576151106690333169295044378117/80000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (445196635350311262748579391303/1000000000000000000000000000000), innerHi := (55649579418788907843572423913/125000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (25430618201686351545483709430880849478662375075425328561522259327263741374809984725729657/40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (5244934506623327941099433/1000000000000000000000000)) (.exp (-856841524118642432671221568176763876627127418397367221195923/400000000000000000000000000000000000000000000000000000000000) (117407579740302475785521/1000000000000000000000000) (58703789870151237892761/500000000000000000000000) { parts := 3, inner := (-285613841372880810890407189392254625542375806132455740398641/400000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (244832302108318726569061974407/500000000000000000000000000000), innerHi := (97932920843327490627624789763/200000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell120
