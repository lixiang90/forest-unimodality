import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell190.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell190
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(25413391944076440977736120777/250000000000000000000000000000)]
def alpha : ℚ := (94938245927988596005211723741/500000000000000000000000000000)
def D : ℚ := (755974311332818150907236252357/500000000000000000000000000000)
def mlo : ℚ := (16903438472156410309235872185253/1000000000000000000000000000000)
def mhi : ℚ := (27233317538474216609324460742907/1000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (9256907813042857139237904585825976450221997771080503575351819755398973683169159717651/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1243489944840720839991377/125000000000000000000000)) (.exp (-429573707095491501424607458551468597617485384821462126301581/250000000000000000000000000000000000000000000000000000000000) (5605367090624266243271/31250000000000000000000) (179371746899976519784673/1000000000000000000000000) { parts := 2, inner := (-429573707095491501424607458551468597617485384821462126301581/500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (8470460362931321096771910021/20000000000000000000000000000), innerHi := (423523018146566054838595501051/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (3456915752537820143676714656276512464083017092570553160643861873234987251245713973069/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1243489944840720839991377/125000000000000000000000)) (.exp (-692090972542736307850756460999572765755316184387313698078739/250000000000000000000000000000000000000000000000000000000000) (62764610578340202846599/1000000000000000000000000) (313823052891701014233/5000000000000000000000) { parts := 3, inner := (-230696990847578769283585486999857588585105394795771232692913/250000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (99352382985430784972608895659/250000000000000000000000000000), innerHi := (397409531941723139890435582637/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell190
