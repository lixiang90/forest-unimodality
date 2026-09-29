import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell026.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell026
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(130706845800358047105797636639/1000000000000000000000000000000)]
def R : ℚ := (1406862309090909090909090909091/1000000000000000000000000000000)
def D : ℚ := (1630958385318559556786703601109/1000000000000000000000000000000)
def vmax : ℚ := (836/3969)
def mlo : ℚ := (381315789473684210526315789473683/4000000000000000000000000000000)
def mhi : ℚ := (8770263157894736842105263157894709/80000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (27398465327306282679435114511303642424310132459338228506367525834819344949609712928178204083903/63504000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (104276248936362463837213/2000000000000000000000)) (.exp (-49840584095978634277973888286818525986449820619206135087071437/4000000000000000000000000000000000000000000000000000000000000) (3878174425306972041/1000000000000000000000000) (1939087212653486021/500000000000000000000000) { parts := 13, inner := (-49840584095978634277973888286818525986449820619206135087071437/52000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (383478097827657671613199825339/1000000000000000000000000000000), innerHi := (19173904891382883580659991267/50000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (10448849316169109687457721910359963593629658516610566844278627391151750524131164430678260132857579/25401600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (104276248936362463837213/2000000000000000000000)) (.exp (-1146333434207508588393399430596826097688345874241741107002643051/80000000000000000000000000000000000000000000000000000000000000) (598303355848125841/1000000000000000000000000) (299151677924062921/500000000000000000000000) { parts := 15, inner := (-1146333434207508588393399430596826097688345874241741107002643051/1200000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (96176308699088741357692753487/250000000000000000000000000000), innerHi := (384705234796354965430771013949/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell026
