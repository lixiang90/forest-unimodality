import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell213.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell213
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(28483888980696271497849592881/1000000000000000000000000000000)]
def alpha : ℚ := (33011579513888888888888888889/125000000000000000000000000000)
def D : ℚ := (1015245775742725880551301684533/500000000000000000000000000000)
def mlo : ℚ := (15428571428571428571428571428571/1000000000000000000000000000000)
def mhi : ℚ := (5142857142857142857142857142857/200000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (16638898088831603409913699004981492739681019972785189767543313433438293762529107466279/625000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (4045715293807389656421947/100000000000000000000000)) (.exp (-439465715702171045966822290163987792619008273026500921603051/1000000000000000000000000000000000000000000000000000000000000) (80547576446219319669361/125000000000000000000000) (644380611569754557354889/1000000000000000000000000) { parts := 1, inner := (-439465715702171045966822290163987792619008273026500921603051/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (644380611569754557354888377861/1000000000000000000000000000000), innerHi := (322190305784877278677444188931/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (2500191026893913251201047250234698175555255389968245337514437811146097920843035822093/125000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (4045715293807389656421947/100000000000000000000000)) (.exp (-146488571900723681988940763387995930873002757675500307201017/200000000000000000000000000000000000000000000000000000000000) (480733190874746560222247/1000000000000000000000000) (60091648859343320027781/125000000000000000000000) { parts := 1, inner := (-146488571900723681988940763387995930873002757675500307201017/200000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (60091648859343320027780921043/125000000000000000000000000000), innerHi := (96146638174949312044449473669/200000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell213
