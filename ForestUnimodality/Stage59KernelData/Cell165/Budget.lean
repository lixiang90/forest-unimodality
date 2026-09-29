import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell165.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell165
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(50198462338149975325321192771/500000000000000000000000000000)]
def alpha : ℚ := (174053201200919125988912364739/1000000000000000000000000000000)
def D : ℚ := (299910386763395810363836824697/200000000000000000000000000000)
def mlo : ℚ := (17053755242089210827296988181471/1000000000000000000000000000000)
def mhi : ℚ := (3434436819587410513830643453213/125000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (3585988117446113464864834313570892051033942587390174790721597034363488797090515678291/2000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (2413652856301621074663899/250000000000000000000000)) (.exp (-856072290244042964640590009543382897068057994277035921346141/500000000000000000000000000000000000000000000000000000000000) (45119581747856753070939/250000000000000000000000) (180478326991427012283757/1000000000000000000000000) { parts := 2, inner := (-856072290244042964640590009543382897068057994277035921346141/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (424827408474814642912949001209/1000000000000000000000000000000), innerHi := (42482740847481464291294900121/100000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (165637021981009778583878430221379734083507390938210066708066531756627211028658839673/250000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (2413652856301621074663899/250000000000000000000000)) (.exp (-172403447340814208156785488033046920798500540164675492323223/62500000000000000000000000000000000000000000000000000000000) (12677923947860523670841/200000000000000000000000) (31694809869651309177103/500000000000000000000000) { parts := 3, inner := (-172403447340814208156785488033046920798500540164675492323223/187500000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (398724310321568752800993568999/1000000000000000000000000000000), innerHi := (398724310321568752800993569/1000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell165
