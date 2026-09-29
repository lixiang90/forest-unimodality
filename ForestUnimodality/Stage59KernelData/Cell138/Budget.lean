import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell138.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell138
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(12316981763687316804158578353/125000000000000000000000000000)]
def alpha : ℚ := (17213858631316863905325443787/100000000000000000000000000000)
def D : ℚ := (11507826440637454659442031257/7812500000000000000000000000)
def mlo : ℚ := (1637037037037037037037037037037/100000000000000000000000000000)
def mhi : ℚ := (8859259259259259259259259259259/400000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (322415539460360009457225331373440835887537800206841358198195195166937350638997381314657/250000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (3146842106864831567492047/500000000000000000000000)) (.exp (-20163355331665903805326265303799543815490233803081327460061/12500000000000000000000000000000000000000000000000000000000) (49818803412448078774601/250000000000000000000000) (39855042729958463019681/200000000000000000000000) { parts := 2, inner := (-20163355331665903805326265303799543815490233803081327460061/25000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (446402524242182478161517049511/1000000000000000000000000000000), innerHi := (55800315530272809770189631189/125000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (2980954418535253162235374237990585940944945278577817830088118962143064038287730050374061/4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (3146842106864831567492047/500000000000000000000000)) (.exp (-109119334736074302946471553408796806708431636621569292220427/50000000000000000000000000000000000000000000000000000000000) (7048253544991923896771/62500000000000000000000) (112772056719870782348337/1000000000000000000000000) { parts := 3, inner := (-36373111578691434315490517802932268902810545540523097406809/50000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (943620149677250810962360013/1953125000000000000000000000), innerHi := (483133516634752415212728326657/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell138
