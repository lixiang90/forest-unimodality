import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell169.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell169
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(100618064268314549599121163843/1000000000000000000000000000000)]
def alpha : ℚ := (43633196100550373798504805981/250000000000000000000000000000)
def D : ℚ := (749313433505222056442652614203/500000000000000000000000000000)
def mlo : ℚ := (8517857142857142857142857142857/500000000000000000000000000000)
def mhi : ℚ := (6861607142857142857142857142857/250000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (2243137280838990364751946856132647321714938381405675150162467128999574979258690145429/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1924779681143932208442493/200000000000000000000000)) (.exp (-857050297428322145692514199162682054562247383635771554119451/500000000000000000000000000000000000000000000000000000000000) (180125653819957532974053/1000000000000000000000000) (90062826909978766487027/500000000000000000000000) { parts := 2, inner := (-857050297428322145692514199162682054562247383635771554119451/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (21220606366216160328335077417/50000000000000000000000000000), innerHi := (424412127324323206566701548341/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (418209135535762603782313228721015074456193664629401236381217128999574979258690145429/625000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1924779681143932208442493/200000000000000000000000)) (.exp (-690401628483926172918969771547713304562247383635771554119451/250000000000000000000000000000000000000000000000000000000000) (15797542720621992966747/250000000000000000000000) (63190170882487971866989/1000000000000000000000000) { parts := 3, inner := (-230133876161308724306323257182571101520749127878590518039817/250000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (12447052794290680478716328669/31250000000000000000000000000), innerHi := (398305689417301775318922517409/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell169
