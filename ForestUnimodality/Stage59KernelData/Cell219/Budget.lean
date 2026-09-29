import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell219.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell219
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(2988298433148563212873644183/100000000000000000000000000000)]
def alpha : ℚ := (77464589556672237357203360729/250000000000000000000000000000)
def D : ℚ := (470607184888888888888888888889/200000000000000000000000000000)
def mlo : ℚ := (3847868217054263565891472868217/250000000000000000000000000000)
def mhi : ℚ := (251124031007751937984496124031/10000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (2466373941981605728391145478285480778163018116031619124272386617346687676484764928537059/250000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (28187560211762082928999/2000000000000000000000)) (.exp (-11498578563985411354962442878578326216364092713624107631711/25000000000000000000000000000000000000000000000000000000000) (631319539699708040428023/1000000000000000000000000) (78914942462463505053503/125000000000000000000000) { parts := 1, inner := (-11498578563985411354962442878578326216364092713624107631711/25000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (126263907939941608085604679271/200000000000000000000000000000), innerHi := (157829884924927010107005849089/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (15244723259943967753334359797277248308783565355686293747783022563502406699212986917241/2000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (28187560211762082928999/2000000000000000000000)) (.exp (-750433548386416320008075219444046602337727530517729661673/1000000000000000000000000000000000000000000000000000000000) (94432360674372647541333/200000000000000000000000) (236080901685931618853333/500000000000000000000000) { parts := 1, inner := (-750433548386416320008075219444046602337727530517729661673/1000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (118040450842965809426666484037/250000000000000000000000000000), innerHi := (472161803371863237706665936149/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell219
