import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage130KernelData.Cell017.Parameters

namespace ForestUnimodality.Stage130KernelData.Cell017
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(6460752661446166348280518249/62500000000000000000000000000), (107967886314637728031473312937/500000000000000000000000000000)]
def R : ℚ := (1386175903846153846153846153847/1000000000000000000000000000000)
def D : ℚ := (2296765958762886597938144329897/1000000000000000000000000000000)
def vmax : ℚ := (1716/7225)
def mlo : ℚ := (85/2)
def mhi : ℚ := (3420928030303030303030303030303/62500000000000000000000000000)
def alpha : ℚ := (594669462750000000000000000000363/1806250000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (3364773966379373445392201912191070966563021598190808450129/8500000000000000000000000000000000000000000000000000000000)) (.mul (.rat (6422972481903771457822927/2500000000000000000000000)) (.exp (-109832795244584827920768810233/25000000000000000000000000000) (3089932073799433419199/250000000000000000000000) (12359728295197733676797/1000000000000000000000000) { parts := 5, inner := (-109832795244584827920768810233/125000000000000000000000000000), terms := 40, innerLo := (207669056164968405183210020363/500000000000000000000000000000), innerHi := (415338112329936810366420040727/1000000000000000000000000000000) }))) (.mul (.rat (369817024099824975813533/31250000000000000000000)) (.exp (-1835454067348841376535046319929/200000000000000000000000000000) (103362292672788762423/1000000000000000000000000) (12920286584098595303/125000000000000000000000) { parts := 10, inner := (-1835454067348841376535046319929/2000000000000000000000000000000), terms := 40, innerLo := (99856472918750282948539840757/250000000000000000000000000000), innerHi := (399425891675001131794159363029/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (41987396516702754363387608331334224672229721318579833141401355988949078651403603833238923/112890625000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (6422972481903771457822927/2500000000000000000000000)) (.exp (-22101769876396094633677435771318459522646622843443991499447/3906250000000000000000000000000000000000000000000000000000) (1744651827685430001573/500000000000000000000000) (3489303655370860003147/1000000000000000000000000) { parts := 6, inner := (-22101769876396094633677435771318459522646622843443991499447/23437500000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (194727130995721745173205022099/500000000000000000000000000000), innerHi := (389454261991443490346410044199/1000000000000000000000000000000) }))) (.mul (.rat (369817024099824975813533/31250000000000000000000)) (.exp (-369350368666315144425849756614497201730717738250665712929911/31250000000000000000000000000000000000000000000000000000000) (7361757983273709831/1000000000000000000000000) (920219747909213729/125000000000000000000000) { parts := 12, inner := (-369350368666315144425849756614497201730717738250665712929911/375000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (373463756558807687399980575911/1000000000000000000000000000000), innerHi := (46682969569850960924997571989/125000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck = true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mhi := by
  norm_num [budgetExpression_hi, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_hi_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mhi := by
  rw [← budgetExpression_hi_eval]
  exact budgetExpression_hi.positiveCheck_sound budgetExpression_hi_checked

theorem budget_positive {m : ℝ} (hm : m ∈ Set.Icc (mlo : ℝ) (mhi : ℝ)) :
    0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D m := by
  have hs := row.signCheck_sound row_checked
  have hdM : (0 : ℝ) ≤ row.dM := by norm_num [row]
  have hT : ∀ i ∈ row.terms, (0 : ℝ) ≤ row.price i := by
    intro i hi
    exact hs.price i hi
  exact KernelBudget.budget_pos_of_endpoints row.terms (∅ : Finset ℤ)
    row.A row.B row.dδ row.dM alpha varianceIntercept D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ)) (fun _ => 0) (fun _ => 0)
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage130KernelData.Cell017
