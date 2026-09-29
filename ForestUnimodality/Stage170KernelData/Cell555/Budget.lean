import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell555.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell555
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(1212818922395377816663534069/10000000000000000000000000000)]
def R : ℚ := (67493749/31250000)
def D : ℚ := (2771618635428571428571428571429/1000000000000000000000000000000)
def vmax : ℚ := (595/2704)
def mlo : ℚ := (40115484958451957419096200900857/1000000000000000000000000000000)
def mhi : ℚ := (5309402420971582599586261883937/125000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (54141820767004790103984792887918363932959140459685245890717684188796526609101932706670731/211250000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (34720070972384267093957533/5000000000000000000000000)) (.exp (-48652819238677690643089733220549991469539713674499110797133/10000000000000000000000000000000000000000000000000000000000) (24092669842109159319/3125000000000000000000) (7709654349474930982081/1000000000000000000000000) { parts := 5, inner := (-48652819238677690643089733220549991469539713674499110797133/50000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (5905096613673909529457492479/15625000000000000000000000000), innerHi := (377926183275130209885279518657/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (526832357261139595894227017114217525782068490240116565368683114886131205677489418440049/2112500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (34720070972384267093957533/5000000000000000000000000)) (.exp (-6439343722766164938055994102719905318862126605940323349653/1250000000000000000000000000000000000000000000000000000000) (5790857036600183583923/1000000000000000000000000) (1447714259150045895981/250000000000000000000000) { parts := 6, inner := (-2146447907588721646018664700906635106287375535313441116551/2500000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (423763753983737125681851029831/1000000000000000000000000000000), innerHi := (52970469247967140710231378729/125000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell555
