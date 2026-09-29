import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell353.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell353
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(6268543550698558674211104133/50000000000000000000000000000), (28327751341581598754635877353/200000000000000000000000000000)]
def R : ℚ := (8458603/6250000)
def D : ℚ := (63356039/40000000)
def vmax : ℚ := (10/49)
def mlo : ℚ := (315/4)
def mhi : ℚ := (175/2)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (14758392538908582353295531466964102073/32000000000000000000000000000000000000)) (.mul (.rat (69451572974842541441375943/10000000000000000000000000)) (.exp (-394918243694009196475299560379/40000000000000000000000000000) (51550116253169013851/1000000000000000000000000) (12887529063292253463/250000000000000000000000) { parts := 10, inner := (-394918243694009196475299560379/400000000000000000000000000000), terms := 40, innerLo := (372582939625155428068153564011/1000000000000000000000000000000), innerHi := (93145734906288857017038391003/250000000000000000000000000000) }))) (.mul (.rat (5261066694983490901749157/250000000000000000000000000)) (.exp (-1784648334519640721542060273239/160000000000000000000000000000) (2863430996009834693/200000000000000000000000) (7158577490024586733/500000000000000000000000) { parts := 12, inner := (-594882778173213573847353424413/640000000000000000000000000000), terms := 40, innerLo := (78949864596976984812389845221/200000000000000000000000000000), innerHi := (197374661492442462030974613053/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (1422456564543793289382153138601566897/3200000000000000000000000000000000000)) (.mul (.rat (69451572974842541441375943/10000000000000000000000000)) (.exp (-43879804854889910719477728931/4000000000000000000000000000) (8605591476554935083/500000000000000000000000) (17211182953109870167/1000000000000000000000000) { parts := 11, inner := (-43879804854889910719477728931/44000000000000000000000000000), terms := 40, innerLo := (368885754177107309975284764757/1000000000000000000000000000000), innerHi := (184442877088553654987642382379/500000000000000000000000000000) }))) (.mul (.rat (5261066694983490901749157/250000000000000000000000000)) (.exp (-198294259391071191282451141471/16000000000000000000000000000) (129559303992801663/31250000000000000000000) (4145897727769653217/1000000000000000000000000) { parts := 13, inner := (-198294259391071191282451141471/208000000000000000000000000000), terms := 40, innerLo := (385452316770711661058752913639/1000000000000000000000000000000), innerHi := (9636307919267791526468822841/25000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell353
