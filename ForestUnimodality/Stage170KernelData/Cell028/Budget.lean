import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell028.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell028
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(21815599574672253172584937847/200000000000000000000000000000)]
def R : ℚ := (1406862309090909090909090909091/1000000000000000000000000000000)
def D : ℚ := (1630958385318559556786703601109/1000000000000000000000000000000)
def vmax : ℚ := (836/3969)
def mlo : ℚ := (201716052631578947368421052631578307/1600000000000000000000000000000000)
def mhi : ℚ := (525/4)

def budgetExpression_lo : Expr := (.sub (.rat (1064167475893448628961912626062074978178673348059776114656600477976611526547275102409159894896024319/2540160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (50864837089607590314699337/1000000000000000000000000)) (.exp (-4400556631994039519500783985110587872084209208562928903108485029/320000000000000000000000000000000000000000000000000000000000000) (1065848380000717449/1000000000000000000000000) (21316967600014349/20000000000000000000000) { parts := 14, inner := (-628650947427719931357254855015798267440601315508989843301212147/640000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (187230596413187428670421218453/500000000000000000000000000000), innerHi := (374461192826374857340842436907/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (3097456446843550812539030695597903830465305003672988964510679/7560000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (50864837089607590314699337/1000000000000000000000000)) (.exp (-458127591068117316624283694787/32000000000000000000000000000) (60593857289253451/100000000000000000000000) (605938572892534511/1000000000000000000000000) { parts := 15, inner := (-152709197022705772208094564929/160000000000000000000000000000), terms := 40, innerLo := (385030594586997435429625250801/1000000000000000000000000000000), innerHi := (192515297293498717714812625401/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell028
