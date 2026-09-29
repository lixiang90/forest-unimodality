import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell419.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell419
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(1124634877104212079569998359/10000000000000000000000000000)]
def R : ℚ := (1706358982962962962962962962963/1000000000000000000000000000000)
def D : ℚ := (1157460523940042826552462526767/500000000000000000000000000000)
def vmax : ℚ := (128425/550564)
def mlo : ℚ := (877471333098215581973167948971/20000000000000000000000000000)
def mhi : ℚ := (97496814788690620219240883219/2000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (1876996160274951358780674726290472330725308882016620094977114922430548963250432861617890709/5618000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (2302315837533063458408833/200000000000000000000000)) (.exp (-986834864861380822337100930514486883298369533653865738589/200000000000000000000000000000000000000000000000000000000) (7196400386410029115021/1000000000000000000000000) (3598200193205014557511/500000000000000000000000) { parts := 5, inner := (-986834864861380822337100930514486883298369533653865738589/1000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (372754644671332215074536343419/1000000000000000000000000000000), innerHi := (18637732233566610753726817171/50000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (176941860827578519218775455880659757516198132923698982084641406408789185938483677818841851/561800000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (2302315837533063458408833/200000000000000000000000)) (.exp (-109648318317931202481900103390498542588707725961540637621/20000000000000000000000000000000000000000000000000000000) (1039817276418660076531/250000000000000000000000) (33274152845397122449/8000000000000000000000) { parts := 6, inner := (-36549439439310400827300034463499514196235908653846879207/40000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (401023204814190795876786810867/1000000000000000000000000000000), innerHi := (100255801203547698969196702717/250000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell419
