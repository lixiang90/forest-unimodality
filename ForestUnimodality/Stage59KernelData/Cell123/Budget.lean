import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell123.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell123
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(17696537733462881084221267669/125000000000000000000000000000)]
def alpha : ℚ := (176537869869176453954189838817/1000000000000000000000000000000)
def D : ℚ := (1477242057571150458885695744879/1000000000000000000000000000000)
def mlo : ℚ := (43726415094339622641509433962263/2000000000000000000000000000000)
def mhi : ℚ := (1088301886792452830188679245283/40000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (201182767085437546350553979761228963816556864656762934366443403394822561134084260476331/500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (3696984846924991074956779/500000000000000000000000)) (.exp (-773806154666042017220429958922762651154684127627431367974947/250000000000000000000000000000000000000000000000000000000000) (45264843989492792312613/1000000000000000000000000) (22632421994746396156307/500000000000000000000000) { parts := 4, inner := (-773806154666042017220429958922762651154684127627431367974947/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (461254118501813364533733055167/1000000000000000000000000000000), innerHi := (7207095601590833820839578987/15625000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (2247319057849497197252906358034707583163062742159576905899208400788312855187041534283/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (3696984846924991074956779/500000000000000000000000)) (.exp (-19259175405021490206375145644300043461552198813564448655327/5000000000000000000000000000000000000000000000000000000000) (10620361103174560641159/500000000000000000000000) (21240722206349121282319/1000000000000000000000000) { parts := 4, inner := (-19259175405021490206375145644300043461552198813564448655327/20000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (23860104264169066153083736217/62500000000000000000000000000), innerHi := (381761668226705058449339779473/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell123
