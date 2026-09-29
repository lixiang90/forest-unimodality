import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell322.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell322
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(115176453448796176308624641393/1000000000000000000000000000000)]
def R : ℚ := (950083027272727272727272727273/500000000000000000000000000000)
def D : ℚ := (1427449926666666666666666666667/500000000000000000000000000000)
def vmax : ℚ := (45/196)
def mlo : ℚ := (69225136471942959661127839106501/1250000000000000000000000000000)
def mhi : ℚ := (1592178138854688072205940299449523/25000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (660226957238802122469685554155905601071404225087924289323912817107235316177528266542380471/2187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (5528634724124931842936803/500000000000000000000000)) (.exp (-7973105708347300665141500992912785590460549686348872659995893/1250000000000000000000000000000000000000000000000000000000000) (1697693749877762112743/1000000000000000000000000) (212211718734720264093/125000000000000000000000) { parts := 7, inner := (-1139015101192471523591642998987540798637221383764124665713699/1250000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (20101831382550513526058412259/50000000000000000000000000000), innerHi := (402036627651010270521168245181/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (126987448484836393120488611943889721213880519909289029048741943795280715985201340395367273557/437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (5528634724124931842936803/500000000000000000000000)) (.exp (-183381431291987915298254522836994068580592642786024071179905539/25000000000000000000000000000000000000000000000000000000000000) (81517014440958015531/125000000000000000000000) (652136115527664124249/1000000000000000000000000) { parts := 8, inner := (-183381431291987915298254522836994068580592642786024071179905539/200000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (399753506145927355899516926167/1000000000000000000000000000000), innerHi := (49969188268240919487439615771/125000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell322
