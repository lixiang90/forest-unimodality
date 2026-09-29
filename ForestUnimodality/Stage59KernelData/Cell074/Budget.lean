import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell074.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell074
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(23583638158447074819725156197/250000000000000000000000000000)]
def alpha : ℚ := (6320165846404933903673469387759077/34151040000000000000000000000000000)
def D : ℚ := (1627341600829809503872723466611/1000000000000000000000000000000)
def mlo : ℚ := (39500782962730974005637331663011/2000000000000000000000000000000)
def mhi : ℚ := (2785311619166927654243658001879/125000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (6174584610331881235634336804119125437995713464595025243347925081602891296913727190581/5519360000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (7175701729983566146131579/1000000000000000000000000)) (.exp (-931572172368398295869920153618128217650655435809985742329167/500000000000000000000000000000000000000000000000000000000000) (155183910706244806884187/1000000000000000000000000) (38795977676561201721047/250000000000000000000000) { parts := 2, inner := (-931572172368398295869920153618128217650655435809985742329167/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (393933891289191830159842398911/1000000000000000000000000000000), innerHi := (6155217051393622346247537483/15625000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (2738626726572031032049406922162543974509536423827366144385966238600031589296394637481/3104640000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (7175701729983566146131579/1000000000000000000000000)) (.exp (-65687781384951161888263600575637699647895417532912194494163/31250000000000000000000000000000000000000000000000000000000) (122210659717488007946157/1000000000000000000000000) (61105329858744003973079/500000000000000000000000) { parts := 3, inner := (-65687781384951161888263600575637699647895417532912194494163/93750000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (496252867774802108849226533827/1000000000000000000000000000000), innerHi := (124063216943700527212306633457/250000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell074
