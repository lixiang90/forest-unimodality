import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell214.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell214
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(28059139813600300717505621497/500000000000000000000000000000)]
def alpha : ℚ := (269879409012345679012345679013/1000000000000000000000000000000)
def D : ℚ := (505665267142857142857142857143/250000000000000000000000000000)
def mlo : ℚ := (1528301886792452830188679245283/100000000000000000000000000000)
def mhi : ℚ := (6367924528301886792452830188679/250000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (4339569716629359055231585044510528752453259323227392293453404146703453072794226681233/500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1894063604560113844854641/100000000000000000000000)) (.exp (-42882836318898572794678402665225885676607290560363820648651/50000000000000000000000000000000000000000000000000000000000) (84830965909605367217197/200000000000000000000000) (212077414774013418042993/500000000000000000000000) { parts := 1, inner := (-42882836318898572794678402665225885676607290560363820648651/50000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (424154829548026836085985855737/1000000000000000000000000000000), innerHi := (212077414774013418042992927869/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (6475792949974266625618747062094215537972038755727651121394253907144889946324946856029/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1894063604560113844854641/100000000000000000000000)) (.exp (-178678484662077386644493344438436513795894777284729668432463/125000000000000000000000000000000000000000000000000000000000) (239445875484585310078003/1000000000000000000000000) (59861468871146327519501/250000000000000000000000) { parts := 2, inner := (-178678484662077386644493344438436513795894777284729668432463/250000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (244666035385270277443838128929/500000000000000000000000000000), innerHi := (489332070770540554887676257859/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell214
