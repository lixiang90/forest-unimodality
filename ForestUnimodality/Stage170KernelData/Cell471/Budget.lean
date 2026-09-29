import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell471.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell471
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(31109504981506797837834438781/250000000000000000000000000000), (91268726243664103012039491287/500000000000000000000000000000)]
def R : ℚ := (163547502998974358974358974359/200000000000000000000000000000)
def D : ℚ := (410175389905813575836310490419/250000000000000000000000000000)
def vmax : ℚ := (22576125/90364036)
def mlo : ℚ := (43854838188538453092064677403687/1000000000000000000000000000000)
def mhi : ℚ := (735/16)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (5812891474640806420142794284333479445425796312507885779981040042653672910607582108751186508447/90364036000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (301935780064955319734743/78125000000000000000000)) (.exp (-1364302307089511560750151397201539489607006477610909825185547/250000000000000000000000000000000000000000000000000000000000) (4265443027195260577657/1000000000000000000000000) (2132721513597630288829/500000000000000000000000) { parts := 6, inner := (-1364302307089511560750151397201539489607006477610909825185547/1500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (402711493113968405740723844633/1000000000000000000000000000000), innerHi := (201355746556984202870361922317/500000000000000000000000000000) }))) (.mul (.rat (44055427879253862499808747/500000000000000000000000)) (.exp (-4002575221089902225671860812184719799582132640203155418175169/500000000000000000000000000000000000000000000000000000000000) (333739288822748765879/1000000000000000000000000) (8343482220568719147/25000000000000000000000) { parts := 9, inner := (-4002575221089902225671860812184719799582132640203155418175169/4500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (410877090026003592422669136587/1000000000000000000000000000000), innerHi := (102719272506500898105667284147/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (325639205697825449247658949398167019039952690223389134787772711/5901324800000000000000000000000000000000000000000000000000000000)) (.mul (.rat (301935780064955319734743/78125000000000000000000)) (.exp (-4573097232281499282161662500807/800000000000000000000000000000) (41145410212792132921/12500000000000000000000) (3291632817023370633681/1000000000000000000000000) { parts := 6, inner := (-1524365744093833094053887500269/1600000000000000000000000000000), terms := 40, innerLo := (385687204116941723237840079429/1000000000000000000000000000000), innerHi := (38568720411694172323784007943/100000000000000000000000000000) }))) (.mul (.rat (44055427879253862499808747/500000000000000000000000)) (.exp (-13416502757818623142769805219189/1600000000000000000000000000000) (228194043350246120779/1000000000000000000000000) (11409702167512306039/50000000000000000000000) { parts := 9, inner := (-4472167585939541047589935073063/4800000000000000000000000000000), terms := 40, innerLo := (393882916376487969109997053213/1000000000000000000000000000000), innerHi := (196941458188243984554998526607/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell471
