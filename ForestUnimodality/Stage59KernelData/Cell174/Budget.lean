import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell174.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell174
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(100783983257196478189321729067/1000000000000000000000000000000)]
def alpha : ℚ := (173833412645474364505779870597/1000000000000000000000000000000)
def D : ℚ := (376651473469494577279008416733/250000000000000000000000000000)
def mlo : ℚ := (17013427665386346272593119760541/1000000000000000000000000000000)
def mhi : ℚ := (548210446995782268783556081173/20000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (9504444621450142073950482614277088156091560201018659431315243343854915980764342319199/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (507471443274587041827317/50000000000000000000000)) (.exp (-1714681008975820888635280661429982727147268521431427119345247/1000000000000000000000000000000000000000000000000000000000000) (36004227336360000830669/200000000000000000000000) (90010568340900002076673/500000000000000000000000) { parts := 2, inner := (-1714681008975820888635280661429982727147268521431427119345247/2000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (424288977799093909190568727059/1000000000000000000000000000000), innerHi := (21214448889954695459528436353/50000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (71452189956994874377249874767367405650609959489483667631399066652403686492652295047/100000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (507471443274587041827317/50000000000000000000000)) (.exp (-55250832511443117522692376868300675234540684758634965555591/20000000000000000000000000000000000000000000000000000000000) (63131108637586494776277/1000000000000000000000000) (31565554318793247388139/500000000000000000000000) { parts := 3, inner := (-18416944170481039174230792289433558411513561586211655185197/20000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (398181555336497803665869492057/1000000000000000000000000000000), innerHi := (199090777668248901832934746029/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell174
