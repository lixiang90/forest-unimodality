import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell428.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell428
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(2881515074941480060294078457/25000000000000000000000000000), (137689701209811156000432757581/1000000000000000000000000000000)]
def R : ℚ := (631431/500000)
def D : ℚ := (1456173623456790123456790123457/1000000000000000000000000000000)
def vmax : ℚ := (234/1225)
def mlo : ℚ := (10329861111111111111111111111111/125000000000000000000000000000)
def mhi : ℚ := (175/2)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (72180478578032620759406786953993630671629858747790700605537725682532967804853523117797769/153125000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (51757695391573017573705329/10000000000000000000000000)) (.exp (-29765650513718413817273900727690652053880562057771078435727/3125000000000000000000000000000000000000000000000000000000) (73003135594437522337/1000000000000000000000000) (36501567797218761169/500000000000000000000000) { parts := 10, inner := (-29765650513718413817273900727690652053880562057771078435727/31250000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (19288753174656141363390412621/50000000000000000000000000000), innerHi := (385775063493122827267808252421/1000000000000000000000000000000) }))) (.mul (.rat (2536868252225046686809673/31250000000000000000000000)) (.exp (-1422315489927736767712803659039828451144310020982666618582491/125000000000000000000000000000000000000000000000000000000000) (11438520361333706743/1000000000000000000000000) (1429815045166713343/125000000000000000000000) { parts := 12, inner := (-474105163309245589237601219679942817048103340327555539527497/500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (3099470266333842381621151553/8000000000000000000000000000), innerHi := (193716891645865148851321972063/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (32209914189531502090890025486805704358552194780821547550787/70000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (51757695391573017573705329/10000000000000000000000000)) (.exp (-20170605524590360422058549199/2000000000000000000000000000) (20843884901045872993/500000000000000000000000) (41687769802091745987/1000000000000000000000000) { parts := 11, inner := (-20170605524590360422058549199/22000000000000000000000000000), terms := 40, innerLo := (199889036036085160575130884553/500000000000000000000000000000), innerHi := (399778072072170321150261769107/1000000000000000000000000000000) }))) (.mul (.rat (2536868252225046686809673/31250000000000000000000000)) (.exp (-963827908468678092003029303067/80000000000000000000000000000) (5857141594675699153/1000000000000000000000000) (2928570797337849577/500000000000000000000000) { parts := 13, inner := (-963827908468678092003029303067/1040000000000000000000000000000), terms := 40, innerLo := (395835085867384779550788035117/1000000000000000000000000000000), innerHi := (197917542933692389775394017559/500000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck = true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mhi := by
  norm_num [budgetExpression_hi, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

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
end ForestUnimodality.Stage170KernelData.Cell428
