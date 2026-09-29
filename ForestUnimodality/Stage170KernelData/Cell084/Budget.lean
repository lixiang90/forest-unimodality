import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell084.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell084
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(54196053821580075285822330313/500000000000000000000000000000), (34107539458400355632431972723/200000000000000000000000000000)]
def R : ℚ := (9850373/10000000)
def D : ℚ := (90810693/50000000)
def vmax : ℚ := (5696/23409)
def mlo : ℚ := (3825/64)
def mhi : ℚ := (17595/256)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (235224616834983866142523139231170309909/489600000000000000000000000000000000000)) (.mul (.rat (1005005034703573052468073/125000000000000000000000)) (.exp (-8291996234701751518730816537889/1280000000000000000000000000000) (153669379257780375447/100000000000000000000000) (1536693792577803754471/1000000000000000000000000) { parts := 7, inner := (-8291996234701751518730816537889/8960000000000000000000000000000), terms := 40, innerLo := (396354602189937756614957179997/1000000000000000000000000000000), innerHi := (198177301094968878307478589999/500000000000000000000000000000) }))) (.mul (.rat (3210239610701574264339797/200000000000000000000000)) (.exp (-5218453537135254411762091826619/512000000000000000000000000000) (9364483030973120359/250000000000000000000000) (37457932123892481437/1000000000000000000000000) { parts := 11, inner := (-5218453537135254411762091826619/5632000000000000000000000000000), terms := 40, innerLo := (395908559049338050258898062689/1000000000000000000000000000000), innerHi := (39590855904933805025889806269/100000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (9179543618893908810136528052343854177689/19584000000000000000000000000000000000000)) (.mul (.rat (1005005034703573052468073/125000000000000000000000)) (.exp (-190715913398140284930808780371447/25600000000000000000000000000000) (581534436804586732799/1000000000000000000000000) (90864755750716677/156250000000000000000) { parts := 8, inner := (-190715913398140284930808780371447/204800000000000000000000000000000), terms := 40, innerLo := (7881373791242161784549910959/20000000000000000000000000000), innerHi := (394068689562108089227495547951/1000000000000000000000000000000) }))) (.mul (.rat (3210239610701574264339797/200000000000000000000000)) (.exp (-120024431354110851470528112012237/10240000000000000000000000000000) (2030090396625210613/250000000000000000000000) (8120361586500842453/1000000000000000000000000) { parts := 12, inner := (-40008143784703617156842704004079/40960000000000000000000000000000), terms := 40, innerLo := (188264290387803368278485574857/500000000000000000000000000000), innerHi := (75305716155121347311394229943/200000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell084
