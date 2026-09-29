import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell130.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell130
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(97941558567634312076842043781/1000000000000000000000000000000)]
def alpha : ℚ := (171547333613059674671520922309/1000000000000000000000000000000)
def D : ℚ := (366627922014307126311486578553/250000000000000000000000000000)
def mlo : ℚ := (4110981308411214953271028037383/250000000000000000000000000000)
def mhi : ℚ := (2720502336448598130841121495327/125000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (3478646339472517703248084566153573220109583940295802987480731854013908149253626491269/6250000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (838914169095740476223/320000000000000000000)) (.exp (-402635916588206944157017701010892655237263691103462990665123/250000000000000000000000000000000000000000000000000000000000) (99889485720186657024773/500000000000000000000000) (199778971440373314049547/1000000000000000000000000) { parts := 2, inner := (-402635916588206944157017701010892655237263691103462990665123/500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (223483204872521300864948068131/500000000000000000000000000000), innerHi := (446966409745042601729896136263/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (537324212956682386036346902275662102734347176747233323977427674113998083384570770291/1562500000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (838914169095740476223/320000000000000000000)) (.exp (-266450238918666360103908772727798050400521084323057520911387/125000000000000000000000000000000000000000000000000000000000) (59323539718327740489999/500000000000000000000000) (118647079436655480979999/1000000000000000000000000) { parts := 3, inner := (-88816746306222120034636257575932683466840361441019173637129/125000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (245690872032565768647577331247/500000000000000000000000000000), innerHi := (98276348813026307459030932499/200000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell130
