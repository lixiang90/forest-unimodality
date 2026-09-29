import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell137.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell137
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(141315731569886203182366330681/1000000000000000000000000000000)]
def alpha : ℚ := (85822470328088888352051189529/500000000000000000000000000000)
def D : ℚ := (368382978206222541020353268179/250000000000000000000000000000)
def mlo : ℚ := (11086471720926066902512202767453/500000000000000000000000000000)
def mhi : ℚ := (1118287582284716313644709148717/40000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (104715415186291550723028368164560856467693454979293820533644730735065370162551050670523/250000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (7241502177245876303857131/1000000000000000000000000)) (.exp (-1566692861771522417010648749243452363749151910486057142125493/500000000000000000000000000000000000000000000000000000000000) (43570031166056582634001/1000000000000000000000000) (21785015583028291317001/500000000000000000000000) { parts := 4, inner := (-1566692861771522417010648749243452363749151910486057142125493/2000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (45687455116271756133727443421/100000000000000000000000000000), innerHi := (456874551162717561337274434211/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (9706877786514243346123303114576768424731536399027425110094255890822340191468642970857/40000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (7241502177245876303857131/1000000000000000000000000)) (.exp (-158031627796084000324552395575861527675099792511990428886277/40000000000000000000000000000000000000000000000000000000000) (9619741599135113719133/500000000000000000000000) (19239483198270227438267/1000000000000000000000000) { parts := 4, inner := (-158031627796084000324552395575861527675099792511990428886277/160000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (186216583683218187645515585391/500000000000000000000000000000), innerHi := (372433167366436375291031170783/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell137
