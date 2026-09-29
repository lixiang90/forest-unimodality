import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell177.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell177
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(50431518925751057989411777117/500000000000000000000000000000)]
def alpha : ℚ := (87094843055814805839456357399/500000000000000000000000000000)
def D : ℚ := (1506208447858241194991579409827/1000000000000000000000000000000)
def mlo : ℚ := (8500041830502802643687777127081/500000000000000000000000000000)
def mhi : ℚ := (27389023676064586296327281853927/1000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (2447762502408763076873098243712942269448484542892168588601344402098207621654160662343/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (261044533112012189235429/25000000000000000000000)) (.exp (-428670020444677758117813600507343453673908384413636956805477/250000000000000000000000000000000000000000000000000000000000) (180021303596955030152491/1000000000000000000000000) (45005325899238757538123/250000000000000000000000) { parts := 2, inner := (-428670020444677758117813600507343453673908384413636956805477/500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (106072293624724120908041831203/250000000000000000000000000000), innerHi := (424289174498896483632167324813/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (1844172829781267004125467873117588508784399236931198379237123898111470078392594845481/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (261044533112012189235429/25000000000000000000000)) (.exp (-1381270065877294998379621601634739729714420960183059475188459/500000000000000000000000000000000000000000000000000000000000) (63131202944015969325069/1000000000000000000000000) (6313120294401596932507/100000000000000000000000) { parts := 3, inner := (-460423355292431666126540533878246576571473653394353158396153/500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (398181753606747757202454655041/1000000000000000000000000000000), innerHi := (199090876803373878601227327521/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell177
