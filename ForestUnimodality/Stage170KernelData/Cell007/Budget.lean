import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell007.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell007
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(188461072002779512287804599/1600000000000000000000000000)]
def R : ℚ := (256966306796116504854368932039/200000000000000000000000000000)
def D : ℚ := (747246585829072315558802045289/500000000000000000000000000000)
def vmax : ℚ := (3811/19600)
def mlo : ℚ := (575466216216216216216216216216212599/4000000000000000000000000000000000)
def mhi : ℚ := (1225/8)

def budgetExpression_lo : Expr := (.sub (.rat (52183264428486130686405556618761253100841096216766122338078371692556362188989230424316266806728357/112000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (9739717075328705675474339/25000000000000000000000)) (.exp (-108452980009491407311081283055614183160419090918876052353942801/6400000000000000000000000000000000000000000000000000000000000) (21853050655649643/500000000000000000000000) (43706101311299287/1000000000000000000000000) { parts := 17, inner := (-108452980009491407311081283055614183160419090918876052353942801/108800000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (92263668487757823663542154981/250000000000000000000000000000), innerHi := (14762186958041251786166744797/40000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (144567970898230080760134848500074156678896337736637115810497/320000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (9739717075328705675474339/25000000000000000000000)) (.exp (-9234592528136196102102425351/512000000000000000000000000) (1835855827430863/125000000000000000000000) (2937369323889381/200000000000000000000000) { parts := 19, inner := (-9234592528136196102102425351/9728000000000000000000000000), terms := 40, innerLo := (387019709018217403180486214513/1000000000000000000000000000000), innerHi := (193509854509108701590243107257/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell007
