import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell156.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell156
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(12435971410822502200925775373/125000000000000000000000000000)]
def alpha : ℚ := (6899417345112518540894941117/40000000000000000000000000000)
def D : ℚ := (149409862790909090909090909091/100000000000000000000000000000)
def mlo : ℚ := (16209812782440284054228534538411/1000000000000000000000000000000)
def mhi : ℚ := (43861846352485474499677211103937/2000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (1690079154461162081997718117995368852252101589886784017459572041363851961203692551495739/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (8147673576371246895178047/1000000000000000000000000)) (.exp (-201584768337212529220816845604028453610658405793740826352303/125000000000000000000000000000000000000000000000000000000000) (199353001926019591180359/1000000000000000000000000) (4983825048150489779509/25000000000000000000000) { parts := 2, inner := (-201584768337212529220816845604028453610658405793740826352303/250000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (446489643694027455524523298631/1000000000000000000000000000000), innerHi := (55811205461753431940565412329/125000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (3940524675472479121482360583317500544653605400755085273909645026511443468401096150019321/4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (8147673576371246895178047/1000000000000000000000000)) (.exp (-545464667265398608479857346928564405496043269650747017943501/250000000000000000000000000000000000000000000000000000000000) (112831618983355483458951/1000000000000000000000000) (14103952372919435432369/125000000000000000000000) { parts := 3, inner := (-545464667265398608479857346928564405496043269650747017943501/750000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (241609279875001493164244303589/500000000000000000000000000000), innerHi := (483218559750002986328488607179/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell156
