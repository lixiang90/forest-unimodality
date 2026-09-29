import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell054.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell054
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(4765205842305002225998212343/50000000000000000000000000000), (159381574527757424927663723793/1000000000000000000000000000000)]
def R : ℚ := (1269777079268292682926829268293/1000000000000000000000000000000)
def D : ℚ := (2347274758490089635147077389219/1000000000000000000000000000000)
def vmax : ℚ := (14924/65025)
def mlo : ℚ := (7411813186813186813186813186813181/80000000000000000000000000000000)
def mhi : ℚ := (425/4)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (7943962685310649837533542099865789437099432901848834412803543435784980616835268700413721179973521/16646400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (94403129625376838163219873/10000000000000000000000000)) (.exp (-35318815499875454685496090879614532738528674952239807109293083/4000000000000000000000000000000000000000000000000000000000000) (18290195318358007219/125000000000000000000000) (146321562546864057753/1000000000000000000000000) { parts := 9, inner := (-35318815499875454685496090879614532738528674952239807109293083/36000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (93726663343936520251442751697/250000000000000000000000000000), innerHi := (374906653375746081005771006789/1000000000000000000000000000000) }))) (.mul (.rat (3347419625014871336077249/625000000000000000000000)) (.exp (-1181306455819881199759186704453665831726890932047496849075715533/80000000000000000000000000000000000000000000000000000000000000) (193211985893041557/500000000000000000000000) (77284794357216623/200000000000000000000000) { parts := 15, inner := (-393768818606627066586395568151221943908963644015832283025238511/400000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (74731023964146375078746028971/200000000000000000000000000000), innerHi := (46706889977591484424216268107/125000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (11163467080835943425029125543447715080896597493957586897172459/24480000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (94403129625376838163219873/10000000000000000000000000)) (.exp (-81008499319185037841969609831/8000000000000000000000000000) (20011377013728552421/500000000000000000000000) (40022754027457104843/1000000000000000000000000) { parts := 11, inner := (-81008499319185037841969609831/88000000000000000000000000000), terms := 40, innerLo := (12446858323282724570104820497/31250000000000000000000000000), innerHi := (79659893269009437248670851181/200000000000000000000000000000) }))) (.mul (.rat (3347419625014871336077249/625000000000000000000000)) (.exp (-2709486766971876223770283304481/160000000000000000000000000000) (4421099630718571/100000000000000000000000) (44210996307185711/1000000000000000000000000) { parts := 17, inner := (-159381574527757424927663723793/160000000000000000000000000000), terms := 40, innerLo := (184652052640845184181136715413/500000000000000000000000000000), innerHi := (369304105281690368362273430827/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell054
