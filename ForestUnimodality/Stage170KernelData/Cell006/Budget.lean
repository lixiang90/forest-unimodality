import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell006.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell006
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(31661324561213886986690339629/250000000000000000000000000000)]
def R : ℚ := (256966306796116504854368932039/200000000000000000000000000000)
def D : ℚ := (747246585829072315558802045289/500000000000000000000000000000)
def vmax : ℚ := (3811/19600)
def mlo : ℚ := (25020270270270270270270270270270113/200000000000000000000000000000000)
def mhi : ℚ := (575466216216216216216216216216212599/4000000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (466482749822137373394902143440529113769866015609376915575635842744504939582482149797503026674813/980000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (34478588236647101439302787/100000000000000000000000)) (.exp (-792174897636317726430502213825582858452766980983557417538208077/50000000000000000000000000000000000000000000000000000000000000) (32900028469331147/250000000000000000000000) (131600113877324589/1000000000000000000000000) { parts := 16, inner := (-792174897636317726430502213825582858452766980983557417538208077/800000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (74299093009010135691797459149/200000000000000000000000000000), innerHi := (185747732522525339229493647873/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (176924658472802525477082583340444340332956916107478348518314488571929440796373742537813851481973677/392000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (34478588236647101439302787/100000000000000000000000)) (.exp (-18220022645635307707901550917988405744413640562621820603378785771/1000000000000000000000000000000000000000000000000000000000000000) (12222068258085281/1000000000000000000000000) (6111034129042641/500000000000000000000000) { parts := 19, inner := (-18220022645635307707901550917988405744413640562621820603378785771/19000000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (76659137296138146564695591197/200000000000000000000000000000), innerHi := (191647843240345366411738977993/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell006
