import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell187.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell187
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(10130840048582174587767024409/100000000000000000000000000000)]
def alpha : ℚ := (47286437414628579969422271039/250000000000000000000000000000)
def D : ℚ := (756569120892551741231875077457/500000000000000000000000000000)
def mlo : ℚ := (16929597226807527236711786068009/1000000000000000000000000000000)
def mhi : ℚ := (1704716387421591284252228458237/62500000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (922947097561155812533585434117250437258984180325963014991906584253768007459678663019/500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (9984229055763501392561921/1000000000000000000000000)) (.exp (-171511041591707417404108969936418046652097754299432037031681/100000000000000000000000000000000000000000000000000000000000) (89971925475419380909119/500000000000000000000000) (179943850950838761818239/1000000000000000000000000) { parts := 2, inner := (-171511041591707417404108969936418046652097754299432037031681/200000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (424197891261659576178530321931/1000000000000000000000000000000), innerHi := (106049472815414894044632580483/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (21224159492505735367357225855134855519095177468031480560971682950241592621622720167/31250000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (9984229055763501392561921/1000000000000000000000000)) (.exp (-17270209049164983002497083778319696870522888763231216106933/6250000000000000000000000000000000000000000000000000000000) (31543724116766337302579/500000000000000000000000) (63087448233532674605159/1000000000000000000000000) { parts := 3, inner := (-17270209049164983002497083778319696870522888763231216106933/18750000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (398089742297576722573453198807/1000000000000000000000000000000), innerHi := (49761217787197090321681649851/125000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell187
