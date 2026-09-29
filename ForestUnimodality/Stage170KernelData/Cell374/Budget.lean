import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell374.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell374
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(114970320366271622228626960681/1000000000000000000000000000000), (89012327689811778924543952919/500000000000000000000000000000)]
def R : ℚ := (53922541/50000000)
def D : ℚ := (883742337164179104477611940299/500000000000000000000000000000)
def vmax : ℚ := (20/81)
def mlo : ℚ := (405/8)
def mhi : ℚ := (225/4)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (1371637720034205554266124704614982894330348317332019839479/4000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (6963546702395389864648223/1000000000000000000000000)) (.exp (-9312595949668001400518783815161/1600000000000000000000000000000) (2966500011044502882441/1000000000000000000000000) (1483250005522251441221/500000000000000000000000) { parts := 6, inner := (-3104198649889333800172927938387/3200000000000000000000000000000), terms := 40, innerLo := (379059506082702966951013638843/1000000000000000000000000000000), innerHi := (94764876520675741737753409711/250000000000000000000000000000) }))) (.mul (.rat (26459680020011447254546511/1000000000000000000000000)) (.exp (-7209998542874754092888060186439/800000000000000000000000000000) (121877004866677502861/1000000000000000000000000) (60938502433338751431/500000000000000000000000) { parts := 10, inner := (-7209998542874754092888060186439/8000000000000000000000000000000), terms := 40, innerLo := (203030919563263701102065278093/500000000000000000000000000000), innerHi := (406061839126527402204130556187/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (397237908687538929555806148892494298110116105777339946493/1200000000000000000000000000000000000000000000000000000000)) (.mul (.rat (6963546702395389864648223/1000000000000000000000000)) (.exp (-1034732883296444600057642646129/160000000000000000000000000000) (1553755274270154452999/1000000000000000000000000) (1553755274270154453/1000000000000000000000) { parts := 7, inner := (-147818983328063514293948949447/160000000000000000000000000000), terms := 40, innerLo := (396980290429605771083581208153/1000000000000000000000000000000), innerHi := (198490145214802885541790604077/500000000000000000000000000000) }))) (.mul (.rat (26459680020011447254546511/1000000000000000000000000)) (.exp (-801110949208306010320895576271/80000000000000000000000000000) (11193456110985490343/250000000000000000000000) (44773824443941961373/1000000000000000000000000) { parts := 11, inner := (-801110949208306010320895576271/880000000000000000000000000000), terms := 40, innerLo := (201191008336220269988464500017/500000000000000000000000000000), innerHi := (80476403334488107995385800007/200000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell374
