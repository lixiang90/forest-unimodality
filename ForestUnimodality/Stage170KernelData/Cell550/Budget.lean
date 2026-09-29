import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell550.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell550
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(28454796869942295217164016983/250000000000000000000000000000)]
def R : ℚ := (43935559/25000000)
def D : ℚ := (2300991799491525423728813559323/1000000000000000000000000000000)
def vmax : ℚ := (31860/137641)
def mlo : ℚ := (644073695044650172703389484177/15625000000000000000000000000)
def mhi : ℚ := (545568306390762499231106386597/12500000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (69264523200173773595915114115037329960602543990757630850810488830780262347091884348100429731/215064062500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1637656457173968931329/160000000000000000000)) (.exp (-18326986161768680111782445843514738084058323178477637777991/3906250000000000000000000000000000000000000000000000000000) (9171004493722756811811/1000000000000000000000000) (2292751123430689202953/250000000000000000000000) { parts := 5, inner := (-18326986161768680111782445843514738084058323178477637777991/19531250000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (391276154232829954158983242199/1000000000000000000000000000000), innerHi := (1956380771164149770794916211/5000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (7704482391524509100101442867565789036320588265014036533324339890947099287510400845147778329/24578750000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1637656457173968931329/160000000000000000000)) (.exp (-15524035337027587859392189420389289374694931895830671576851/3125000000000000000000000000000000000000000000000000000000) (1739799036015562718779/250000000000000000000000) (6959196144062250875117/1000000000000000000000000) { parts := 5, inner := (-15524035337027587859392189420389289374694931895830671576851/15625000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (370264278694239424819487319269/1000000000000000000000000000000), innerHi := (37026427869423942481948731927/100000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell550
