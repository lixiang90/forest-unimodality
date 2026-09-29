import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell094.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell094
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(748105779492800408682327849/7812500000000000000000000000), (138406247615570965975566115673/1000000000000000000000000000000)]
def alpha : ℚ := (187418723169/1000000000000)
def D : ℚ := (1619335743149367088607594936709/1000000000000000000000000000000)
def mlo : ℚ := (79/4)
def mhi : ℚ := (45/2)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.sub (.rat (10363486697018088272828043888033217221814599212653113/10000000000000000000000000000000000000000000000000000)) (.mul (.rat (3366046224392019503568463/500000000000000000000000)) (.exp (-59100356579931232285903900071/31250000000000000000000000000) (150888909657526022355951/1000000000000000000000000) (9430556853595376397247/62500000000000000000000) { parts := 2, inner := (-59100356579931232285903900071/62500000000000000000000000000), terms := 40, innerLo := (194222108459313934997602350823/500000000000000000000000000000), innerHi := (388444216918627869995204701647/1000000000000000000000000000000) }))) (.mul (.rat (156793770593966277915321/625000000000000000000000)) (.exp (-10934093561630106312069723138167/4000000000000000000000000000000) (64989900998751664775457/1000000000000000000000000) (32494950499375832387729/500000000000000000000000) { parts := 3, inner := (-10934093561630106312069723138167/12000000000000000000000000000000), terms := 40, innerLo := (20102587577110012314579306279/50000000000000000000000000000), innerHi := (402051751542200246291586125581/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (7960157472397260750654483562223171021814599212653113/10000000000000000000000000000000000000000000000000000)) (.mul (.rat (3366046224392019503568463/500000000000000000000000)) (.exp (-6732952015435203678140950641/3125000000000000000000000000) (11595597973526452350607/100000000000000000000000) (115955979735264523506071/1000000000000000000000000) { parts := 3, inner := (-2244317338478401226046983547/3125000000000000000000000000), terms := 40, innerLo := (243819098348505362753405915789/500000000000000000000000000000), innerHi := (487638196697010725506811831579/1000000000000000000000000000000) }))) (.mul (.rat (156793770593966277915321/625000000000000000000000)) (.exp (-1245656228540138693780095041057/400000000000000000000000000000) (2220833185101476883853/50000000000000000000000) (44416663702029537677061/1000000000000000000000000) { parts := 4, inner := (-1245656228540138693780095041057/1600000000000000000000000000000), terms := 40, innerLo := (459078002699717352453737353981/1000000000000000000000000000000), innerHi := (229539001349858676226868676991/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell094
