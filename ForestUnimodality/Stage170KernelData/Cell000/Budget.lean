import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell000.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell000
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(2881515074941480060294078457/25000000000000000000000000000)]
def R : ℚ := (631431/500000)
def D : ℚ := (1456173623456790123456790123457/1000000000000000000000000000000)
def vmax : ℚ := (234/1225)
def mlo : ℚ := (48611111111111111111111111111111/500000000000000000000000000000)
def mhi : ℚ := (1118055555555555555555555555555553/10000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (2395644863982582782242310122452277389119215379935768119411782228119535837725190869778755193/4900000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (71588780763362780401593/3125000000000000000000)) (.exp (-140073649476321947375406591659721902053880562057771078435727/12500000000000000000000000000000000000000000000000000000000) (13593865160886512731/1000000000000000000000000) (3398466290221628183/250000000000000000000000) { parts := 12, inner := (-140073649476321947375406591659721902053880562057771078435727/150000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (196523844220265397379241023899/500000000000000000000000000000), innerHi := (393047688440530794758482047799/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (456093436228720979341465653464018336602799315500064340065417241170826497904137430181720669243/980000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (71588780763362780401593/3125000000000000000000)) (.exp (-3221693937955404789634351608173603747239252927328734804021721/250000000000000000000000000000000000000000000000000000000000) (632826139958447277/250000000000000000000000) (2531304559833789109/1000000000000000000000000) { parts := 13, inner := (-3221693937955404789634351608173603747239252927328734804021721/3250000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (371097501936796717184417418453/1000000000000000000000000000000), innerHi := (185548750968398358592208709227/500000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck = true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mhi := by
  norm_num [budgetExpression_hi, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_hi_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mhi := by
  rw [← budgetExpression_hi_eval]
  exact budgetExpression_hi.positiveCheck_sound budgetExpression_hi_checked

theorem budget_positive {m : ℝ} (hm : m ∈ Set.Icc (mlo : ℝ) (mhi : ℝ)) :
    0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D m := by
  have hs := row.signCheck_sound row_checked
  have hdM : (0 : ℝ) ≤ row.dM := by norm_num [row]
  have hT : ∀ i ∈ row.terms, (0 : ℝ) ≤ row.price i := by
    intro i hi
    exact hs.price i hi
  exact KernelBudget.budget_pos_of_endpoints row.terms (∅ : Finset ℤ)
    row.A row.B row.dδ row.dM (R * vmax : ℚ) 0 D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ)) (fun _ => 0) (fun _ => 0)
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage170KernelData.Cell000
