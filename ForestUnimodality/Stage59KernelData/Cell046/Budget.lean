import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell046.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell046
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(194340200073128356336240233209/1000000000000000000000000000000)]
def alpha : ℚ := (21565895089943849826388888889/125000000000000000000000000000)
def D : ℚ := (43441955580034423407917383821/31250000000000000000000000000)
def mlo : ℚ := (8765217391304347826086956521739/400000000000000000000000000000)
def mhi : ℚ := (13565217391304347826086956521739/500000000000000000000000000000)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha 0 D m

def budgetExpression_lo : Expr := (.sub (.rat (209227104290757642025726524294552948090797586804678090655759740322980581137792428607889/800000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (227469885083690819271851/20000000000000000000000)) (.exp (-1703434101510551158147218739779731173017381765866564838230451/400000000000000000000000000000000000000000000000000000000000) (2828459204755497140901/200000000000000000000000) (7071148011888742852253/500000000000000000000000) { parts := 5, inner := (-1703434101510551158147218739779731173017381765866564838230451/2000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (426681668522422486003901528657/1000000000000000000000000000000), innerHi := (213340834261211243001950764329/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (1590393224461845531548998535117623564581173819374842966909264700593823088517931967461/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (227469885083690819271851/20000000000000000000000)) (.exp (-2636267061861567268561171859182931173017381765866564838230451/500000000000000000000000000000000000000000000000000000000000) (5130592529088277648833/1000000000000000000000000) (2565296264544138824417/500000000000000000000000) { parts := 6, inner := (-878755687287189089520390619727643724339127255288854946076817/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (415299352571991768147407957447/1000000000000000000000000000000), innerHi := (51912419071498971018425994681/125000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell046
