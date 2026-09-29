import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell339.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell339
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(1212818922395377816663534069/10000000000000000000000000000)]
def R : ℚ := (67493749/31250000)
def D : ℚ := (2771618635428571428571428571429/1000000000000000000000000000000)
def vmax : ℚ := (595/2704)
def mlo : ℚ := (24965990050613041734943400325356917/400000000000000000000000000000000)
def mhi : ℚ := (574217771164099959903698207483209091/8000000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (7276970254814132976003909615460179156799400749705687316509027878477233823467297084389794499528363/27040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (4423301826385915624939571/500000000000000000000000)) (.exp (-30279225149718233353169963380789385372290595166533271014305273/4000000000000000000000000000000000000000000000000000000000000) (515792354398382910883/1000000000000000000000000) (128948088599595727721/250000000000000000000000) { parts := 8, inner := (-30279225149718233353169963380789385372290595166533271014305273/32000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (38820342483916175805270992767/100000000000000000000000000000), innerHi := (388203424839161758052709927671/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (2812748163645781406839223261608721524182168604517751062202077402482017845881636731776182222092888427/10816000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (4423301826385915624939571/500000000000000000000000)) (.exp (-696422178443519367122909157758155863562683688830265233329021279/80000000000000000000000000000000000000000000000000000000000000) (5178406713133968147/31250000000000000000000) (33141802964057396141/200000000000000000000000) { parts := 9, inner := (-696422178443519367122909157758155863562683688830265233329021279/720000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (47515725133042080725770543741/125000000000000000000000000000), innerHi := (380125801064336645806164349929/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell339
