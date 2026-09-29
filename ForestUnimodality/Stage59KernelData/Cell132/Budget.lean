import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell132.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell132
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(98052750611246152748228542753/1000000000000000000000000000000)]
def alpha : ℚ := (17065967219325372929584431693/100000000000000000000000000000)
def D : ℚ := (1474595742607476635514018691589/1000000000000000000000000000000)
def mlo : ℚ := (821273730981553790224855257843/50000000000000000000000000000)
def mhi : ℚ := (21739598761276423858893227413491/1000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (41491788083192774162111506690242743267080142841025947898722085050840043689861025965043/50000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (794186197034856622423149/200000000000000000000000)) (.exp (-80528148327501956820128560573070550147128875912217964061779/50000000000000000000000000000000000000000000000000000000000) (24971889463004273473783/125000000000000000000000) (39955023140806837558053/200000000000000000000000) { parts := 2, inner := (-80528148327501956820128560573070550147128875912217964061779/100000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (446962096495926808460645356313/1000000000000000000000000000000), innerHi := (223481048247963404230322678157/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (12691747346869307654190845466168231086972770842878008815859351436994539810478280143893/25000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (794186197034856622423149/200000000000000000000000)) (.exp (-2131627455727992974650461897522438435762127083649402302480723/1000000000000000000000000000000000000000000000000000000000000) (7415253044340024133061/62500000000000000000000) (118644048709440386128977/1000000000000000000000000) { parts := 3, inner := (-710542485242664324883487299174146145254042361216467434160241/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (98275512013833029104869441127/200000000000000000000000000000), innerHi := (122844390017291286381086801409/250000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell132
