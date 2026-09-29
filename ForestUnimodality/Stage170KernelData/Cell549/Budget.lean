import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell549.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell549
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(1124634877104212079569998359/10000000000000000000000000000)]
def R : ℚ := (1706358982962962962962962962963/1000000000000000000000000000000)
def D : ℚ := (1157460523940042826552462526767/500000000000000000000000000000)
def vmax : ℚ := (128425/550564)
def mlo : ℚ := (1657445851407740543727095014723/40000000000000000000000000000)
def mhi : ℚ := (877471333098215581973167948971/20000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (5696326754945902320692186999955033385457630775871076966748060887808108469183993228721002913/17205125000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (2792740331395602293440561/250000000000000000000000)) (.exp (-1864021411404830442192301757638475224008031341346190839557/400000000000000000000000000000000000000000000000000000000) (9465955689625229357317/1000000000000000000000000) (4732977844812614678659/500000000000000000000000) { parts := 5, inner := (-1864021411404830442192301757638475224008031341346190839557/2000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (393761176019931879471291271943/1000000000000000000000000000000), innerHi := (49220147002491484933911408993/125000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (88701083760362897664401281546352285903416117824300372037375561518939035229015544570127958657/275282000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (2792740331395602293440561/250000000000000000000000)) (.exp (-986834864861380822337100930514486883298369533653865738589/200000000000000000000000000000000000000000000000000000000) (7196400386410029115021/1000000000000000000000000) (3598200193205014557511/500000000000000000000000) { parts := 5, inner := (-986834864861380822337100930514486883298369533653865738589/1000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (372754644671332215074536343419/1000000000000000000000000000000), innerHi := (18637732233566610753726817171/50000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell549
