import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell161.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell161
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(143501299895035465987641042043/1000000000000000000000000000000)]
def alpha : ℚ := (21681199150021055145140047289/125000000000000000000000000000)
def D : ℚ := (59721460281633705932932072227/40000000000000000000000000000)
def mlo : ℚ := (85483714032639038007300837449/3906250000000000000000000000)
def mhi : ℚ := (27592656216448357311573974661799/1000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (1140299619289706654795341339125091125392916204916073393368979240873668669819215357981/1953125000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (9721525280025661075455901/1000000000000000000000000)) (.exp (-12267024083539186175715372622637965902866810124916917868307/3906250000000000000000000000000000000000000000000000000000) (21633649138913469245723/500000000000000000000000) (43267298277826938491447/1000000000000000000000000) { parts := 4, inner := (-12267024083539186175715372622637965902866810124916917868307/15625000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (456078862041822673858518670071/1000000000000000000000000000000), innerHi := (57009857755227834232314833759/125000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (87152323292795372071548398171961877326629188736367308450517661651391563432746751509513/250000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (9721525280025661075455901/1000000000000000000000000)) (.exp (-3959582034617170355152648971759321841921004060993442865015357/1000000000000000000000000000000000000000000000000000000000000) (19071083678822424612969/1000000000000000000000000) (1907108367882242461297/100000000000000000000000) { parts := 4, inner := (-3959582034617170355152648971759321841921004060993442865015357/4000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (371615519599113896946366846497/1000000000000000000000000000000), innerHi := (185807759799556948473183423249/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell161
