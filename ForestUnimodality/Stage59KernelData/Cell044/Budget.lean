import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell044.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell044
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(38660805938271872885316216733/200000000000000000000000000000)]
def alpha : ℚ := (34275757600085493983725761773/200000000000000000000000000000)
def D : ℚ := (1391264968027617951668584579977/1000000000000000000000000000000)
def mlo : ℚ := (43951807228915662650602409638553/2000000000000000000000000000000)
def mhi : ℚ := (425129087779690189328743545611/15625000000000000000000000000)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha 0 D m

def budgetExpression_lo : Expr := (.sub (.rat (1121957934069970717579051934908978994873685227585287744814477264701585918783023261246121/4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (580757901350552252495163/50000000000000000000000)) (.exp (-1699212289913443280549801911349157774200002825793235940507349/400000000000000000000000000000000000000000000000000000000000) (14292351788151473146473/1000000000000000000000000) (7146175894075736573237/500000000000000000000000) { parts := 5, inner := (-1699212289913443280549801911349157774200002825793235940507349/2000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (106895826157571380313798946587/250000000000000000000000000000), innerHi := (427583304630285521255195786349/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (2732156871123091669052466871723911722100981260906193854505645350147512662117841091741/15625000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (580757901350552252495163/50000000000000000000000)) (.exp (-16435833161365150779127548249656888214710078404722946908863/3125000000000000000000000000000000000000000000000000000000) (129951914323922476489/25000000000000000000000) (5198076572956899059561/1000000000000000000000000) { parts := 6, inner := (-16435833161365150779127548249656888214710078404722946908863/18750000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (208102413228258037423964753241/500000000000000000000000000000), innerHi := (416204826456516074847929506483/1000000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck=true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval = budget mhi := by
  norm_num [budgetExpression_hi, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
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
    row.A row.B row.dδ row.dM alpha 0 D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ))
    (fun j => (row.fixedPrice j : ℝ)) (fun j => (countBound j : ℝ))
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage59KernelData.Cell044
