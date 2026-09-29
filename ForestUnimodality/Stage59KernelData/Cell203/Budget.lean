import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell203.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell203
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(10084332730090916375162267519/100000000000000000000000000000)]
def alpha : ℚ := (114532984774649665446282035097/500000000000000000000000000000)
def D : ℚ := (70578607587628865979381443299/40000000000000000000000000000)
def mlo : ℚ := (2043367346938775510204081632653/125000000000000000000000000000)
def mhi : ℚ := (13168367346938775510204081632653/500000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (5479849132368048654646872323325882451247346192123935600628229130001725428779709614507/6250000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (4335860950290171267340611/1000000000000000000000000)) (.exp (-20605996216333734735982082353874382591873667903079071697907/12500000000000000000000000000000000000000000000000000000000) (48085526167754927407821/250000000000000000000000) (38468420934203941926257/200000000000000000000000) { parts := 2, inner := (-20605996216333734735982082353874382591873667903079071697907/25000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (438568244029386730552270031409/1000000000000000000000000000000), innerHi := (43856824402938673055227003141/100000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (8683597839738606495477079378464707467917286094555672846968764327556321933433070384353/25000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (4335860950290171267340611/1000000000000000000000000)) (.exp (-132794197838595179409662308502749382591873667903079071697907/50000000000000000000000000000000000000000000000000000000000) (877959062346010630791/12500000000000000000000) (70236724987680850463281/1000000000000000000000000) { parts := 3, inner := (-132794197838595179409662308502749382591873667903079071697907/150000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (412592584030425779626369852561/1000000000000000000000000000000), innerHi := (206296292015212889813184926281/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell203
