import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell020.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell020
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(27355746721479406090470331457/250000000000000000000000000000)]
def alpha : ℚ := (518568029/1445000000)
def D : ℚ := (2258214870770100857762277311717/1000000000000000000000000000000)
def mlo : ℚ := (3642857142857142857142857142857/200000000000000000000000000000)
def mhi : ℚ := (15178571428571428571428571428571/500000000000000000000000000000)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha 0 D m

def budgetExpression_lo : Expr := (.sub (.rat (28615968763561047293173735413490802713460198909045055882583446412234778517780796277527533/14450000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (295916740886132556553889/25000000000000000000000)) (.exp (-99653077342532122186713350307638949179039788656272789952649/50000000000000000000000000000000000000000000000000000000000) (136277565970818709866393/1000000000000000000000000) (68138782985409354933197/500000000000000000000000) { parts := 2, inner := (-99653077342532122186713350307638949179039788656272789952649/100000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (369157914679908643925370784463/1000000000000000000000000000000), innerHi := (23072369667494290245335674029/62500000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (57398580142442274762890663919588347327428222379926590340334601921207141625522450683551541/72250000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (295916740886132556553889/25000000000000000000000)) (.exp (-415221155593883842444638959615166847537119365968818369857947/125000000000000000000000000000000000000000000000000000000000) (7217785019231787278771/200000000000000000000000) (281944727313741690577/7812500000000000000000) { parts := 4, inner := (-415221155593883842444638959615166847537119365968818369857947/500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (435856459491653249380034317173/1000000000000000000000000000000), innerHi := (217928229745826624690017158587/500000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck=true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval = budget mhi := by
  norm_num [budgetExpression_hi, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
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
    row.A row.B row.dδ row.dM alpha 0 D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ))
    (fun j => (row.fixedPrice j : ℝ)) (fun j => (countBound j : ℝ))
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage59KernelData.Cell020
