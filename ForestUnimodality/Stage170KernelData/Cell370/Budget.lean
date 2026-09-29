import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell370.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell370
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(54196053821580075285822330313/500000000000000000000000000000), (16894343014276103910603954467/100000000000000000000000000000)]
def R : ℚ := (9850373/10000000)
def D : ℚ := (90810693/50000000)
def vmax : ℚ := (5696/23409)
def mlo : ℚ := (6885/128)
def mhi : ℚ := (3825/64)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (105698670478729984662043214042064267787/217600000000000000000000000000000000000)) (.mul (.rat (10802304275952433698648747/2000000000000000000000000)) (.exp (-74627966112315763668577348841001/12800000000000000000000000000000) (734291687669824940309/250000000000000000000000) (2937166750679299761237/1000000000000000000000000) { parts := 6, inner := (-24875988704105254556192449613667/25600000000000000000000000000000), terms := 40, innerLo := (47304026964690762034490532153/125000000000000000000000000000), innerHi := (15137288628701043851036970289/40000000000000000000000000000) }))) (.mul (.rat (2176210781497979862564307/125000000000000000000000)) (.exp (-23263510330658195084901645301059/2560000000000000000000000000000) (1413650266182455799/12500000000000000000000) (113092021294596463921/1000000000000000000000000) { parts := 10, inner := (-23263510330658195084901645301059/25600000000000000000000000000000), terms := 40, innerLo := (403035402986840078613238373621/1000000000000000000000000000000), innerHi := (201517701493420039306619186811/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (61333353751520625761191915722403652483/130560000000000000000000000000000000000)) (.mul (.rat (10802304275952433698648747/2000000000000000000000000)) (.exp (-8291996234701751518730816537889/1280000000000000000000000000000) (153669379257780375447/100000000000000000000000) (1536693792577803754471/1000000000000000000000000) { parts := 7, inner := (-8291996234701751518730816537889/8960000000000000000000000000000), terms := 40, innerLo := (396354602189937756614957179997/1000000000000000000000000000000), innerHi := (198177301094968878307478589999/500000000000000000000000000000) }))) (.mul (.rat (2176210781497979862564307/125000000000000000000000)) (.exp (-2584834481184243898322405033451/256000000000000000000000000000) (41202579591445636153/1000000000000000000000000) (20601289795722818077/500000000000000000000000) { parts := 11, inner := (-234984952834931263483855003041/256000000000000000000000000000), terms := 40, innerLo := (399352828049884361055772879627/1000000000000000000000000000000), innerHi := (99838207012471090263943219907/250000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell370
