import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell349.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell349
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(2881515074941480060294078457/25000000000000000000000000000)]
def R : ℚ := (631431/500000)
def D : ℚ := (1456173623456790123456790123457/1000000000000000000000000000000)
def vmax : ℚ := (234/1225)
def mlo : ℚ := (175/2)
def mhi : ℚ := (48611111111111111111111111111111/500000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (133218825665577911852826530620370191976269440525302634759477/280000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (58835522929885657461568371/10000000000000000000000000)) (.exp (-20170605524590360422058549199/2000000000000000000000000000) (20843884901045872993/500000000000000000000000) (41687769802091745987/1000000000000000000000000) { parts := 11, inner := (-20170605524590360422058549199/22000000000000000000000000000), terms := 40, innerLo := (199889036036085160575130884553/500000000000000000000000000000), innerHi := (399778072072170321150261769107/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (5604225017191199558184629992828573084825358963427868968744840637844895269734905394134867709/12250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (58835522929885657461568371/10000000000000000000000000)) (.exp (-140073649476321947375406591659721902053880562057771078435727/12500000000000000000000000000000000000000000000000000000000) (13593865160886512731/1000000000000000000000000) (3398466290221628183/250000000000000000000000) { parts := 12, inner := (-140073649476321947375406591659721902053880562057771078435727/150000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (196523844220265397379241023899/500000000000000000000000000000), innerHi := (393047688440530794758482047799/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell349
