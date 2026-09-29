import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell065.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell065
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(101355061148879007309357280703/1000000000000000000000000000000)]
def R : ℚ := (677985572784810126582278481013/500000000000000000000000000000)
def D : ℚ := (18476581956786703601108033241/8000000000000000000000000000)
def vmax : ℚ := (15326/65025)
def mlo : ℚ := (34766752577319587628865979381443119/400000000000000000000000000000000)
def mhi : ℚ := (799635309278350515463917525773191737/8000000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (715514631473135397061228803575719969182624078315242496226995975212699539435974145824390282843227/1632000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (5004832801475726000717259/200000000000000000000000)) (.exp (-3523786333422173631699935665059565522110283752774942273710832657/400000000000000000000000000000000000000000000000000000000000000) (18664124078868750011/125000000000000000000000) (149312992630950000089/1000000000000000000000000) { parts := 9, inner := (-1174595444474057877233311888353188507370094584258314091236944219/1200000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (187875321884134419872846857807/500000000000000000000000000000), innerHi := (75150128753653767949138743123/200000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (274175231545417488369256004748402450898544054943087894323545935211106117440335393545025341223229883/652800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (5004832801475726000717259/200000000000000000000000)) (.exp (-81047085668709993529098520296370007008536526313823672295349151111/8000000000000000000000000000000000000000000000000000000000000000) (7966035466160540231/200000000000000000000000) (9957544332700675289/250000000000000000000000) { parts := 11, inner := (-81047085668709993529098520296370007008536526313823672295349151111/88000000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (155517522571643479317741757/390625000000000000000000000), innerHi := (398124857783407307053418897921/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell065
