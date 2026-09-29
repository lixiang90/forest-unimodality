import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell088.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell088
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(47734060435258918488836217543/500000000000000000000000000000)]
def alpha : ℚ := (11686914671237992000000000000010981/62726400000000000000000000000000000)
def D : ℚ := (1620907661279187817258883248731/1000000000000000000000000000000)
def mlo : ℚ := (1704303797468354430379746835443/100000000000000000000000000000)
def mhi : ℚ := (73686075949367088607594936708859/4000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (26254243143386149491447721287832581658018916179371696501257777831767810671031611362003857/20908800000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (6384660182813492568243419/1000000000000000000000000)) (.exp (-81353340468395706143505168734042744276186002825880170776549/50000000000000000000000000000000000000000000000000000000000) (196505116593527648194953/1000000000000000000000000) (98252558296763824097477/500000000000000000000000) { parts := 2, inner := (-81353340468395706143505168734042744276186002825880170776549/100000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (2770556102470165421215192411/6250000000000000000000000000), innerHi := (443288976395226467394430785761/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (2762342969557143716569465811788151515734342351541514995301198958615725683273393979318536123/2509056000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (6384660182813492568243419/1000000000000000000000000)) (.exp (-3517335602604167295028017589383607151463284797599114579313437/2000000000000000000000000000000000000000000000000000000000000) (172274214503037341482781/1000000000000000000000000) (86137107251518670741391/500000000000000000000000) { parts := 2, inner := (-3517335602604167295028017589383607151463284797599114579313437/4000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (415059290346617035559712249967/1000000000000000000000000000000), innerHi := (25941205646663564722482015623/62500000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell088
