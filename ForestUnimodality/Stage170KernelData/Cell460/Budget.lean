import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell460.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell460
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(61050341337509617887281494441/500000000000000000000000000000), (46442253935612966428158900499/250000000000000000000000000000)]
def R : ℚ := (32392088649336870026525198939/40000000000000000000000000000)
def D : ℚ := (1661065325469678953626634958383/1000000000000000000000000000000)
def vmax : ℚ := (3179995/12759184)
def mlo : ℚ := (44994072317723770005927682276229/1000000000000000000000000000000)
def mhi : ℚ := (95/2)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (27157635579214942665731845435129869240206935059868779166838632276923829668161656157007246649837/318979600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (44328920011707806381195951/5000000000000000000000000)) (.exp (-2746903473161628657815116677856551641124823352916895689942989/500000000000000000000000000000000000000000000000000000000000) (4112159567224680416227/1000000000000000000000000) (1028039891806170104057/250000000000000000000000) { parts := 6, inner := (-2746903473161628657815116677856551641124823352916895689942989/3000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (100065645619339557977623641023/250000000000000000000000000000), innerHi := (400262582477358231910494564093/1000000000000000000000000000000) }))) (.mul (.rat (43702880783918878648819373/500000000000000000000000)) (.exp (-2089626132177061183597748276453181456040397141111618243938271/250000000000000000000000000000000000000000000000000000000000) (117197301097107627397/500000000000000000000000) (46878920438843050959/200000000000000000000000) { parts := 9, inner := (-2089626132177061183597748276453181456040397141111618243938271/2250000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (395057985779973869691302336019/1000000000000000000000000000000), innerHi := (19752899288998693484565116801/50000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (455998260259809948702798729623387786105413329453048793018614177/6715360000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (44328920011707806381195951/5000000000000000000000000)) (.exp (-1159956485412682739858348394379/200000000000000000000000000000) (757053382754201600309/250000000000000000000000) (3028213531016806401237/1000000000000000000000000) { parts := 6, inner := (-1159956485412682739858348394379/1200000000000000000000000000000), terms := 40, innerLo := (380362549105313256014517772081/1000000000000000000000000000000), innerHi := (190181274552656628007258886041/500000000000000000000000000000) }))) (.mul (.rat (43702880783918878648819373/500000000000000000000000)) (.exp (-882402824776646362135019109481/100000000000000000000000000000) (147154390362016105969/1000000000000000000000000) (14715439036201610597/100000000000000000000000) { parts := 9, inner := (-882402824776646362135019109481/900000000000000000000000000000), terms := 40, innerLo := (75028630707884801302312835829/200000000000000000000000000000), innerHi := (187571576769712003255782089573/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell460
