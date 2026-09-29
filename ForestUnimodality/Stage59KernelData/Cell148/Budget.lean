import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell148.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell148
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(24805288153999522603902243847/250000000000000000000000000000)]
def alpha : ℚ := (21484602083265338483172242211/125000000000000000000000000000)
def D : ℚ := (1487592200669724770642201834863/1000000000000000000000000000000)
def mlo : ℚ := (2035048003491162993672267073969/125000000000000000000000000000)
def mhi : ℚ := (44052803840279293039493781365917/2000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (378524440155548620984833555117943526842921521851546056436292649470514356042625942244717/250000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1837325314459433478475603/250000000000000000000000)) (.exp (-50479952133819724526646250277007323633856591323336224118743/31250000000000000000000000000000000000000000000000000000000) (24852423402623113482649/125000000000000000000000) (198819387220984907861193/1000000000000000000000000) { parts := 2, inner := (-50479952133819724526646250277007323633856591323336224118743/62500000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (445891676554950852629531833747/1000000000000000000000000000000), innerHi := (111472919138737713157382958437/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (35165845157536066865562435619465739071799191046935644953054088965767183875868440018174521/40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1837325314459433478475603/250000000000000000000000)) (.exp (-1092742493249744625047401182466977687140868447554112868762699/500000000000000000000000000000000000000000000000000000000000) (5621159834894343383423/50000000000000000000000) (112423196697886867668461/1000000000000000000000000) { parts := 3, inner := (-1092742493249744625047401182466977687140868447554112868762699/1500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (482634811334078772535894799751/1000000000000000000000000000000), innerHi := (60329351416759846566986849969/125000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck=true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval = budget mhi := by
  norm_num [budgetExpression_hi, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_hi_positive : 0 < budget mhi := by
  rw [← budgetExpression_hi_eval]
  exact budgetExpression_hi.positiveCheck_sound budgetExpression_hi_checked

theorem budget_positive {m : ℝ} (hm : m ∈ Set.Icc (mlo : ℝ) (mhi : ℝ)) :
    0 < budget m := by
  have hs := row.signCheck_sound row_checked
  have hdM : (0 : ℝ) ≤ row.dM := by norm_num [row]
  have hT : ∀ i ∈ row.terms, (0 : ℝ) ≤ row.price i := by
    intro i hi
    exact hs.price i hi
  exact KernelBudget.budget_pos_of_endpoints row.terms row.fixedIndices
    row.A row.B row.dδ row.dM alpha varianceIntercept D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ))
    (fun j => (row.fixedPrice j : ℝ)) (fun j => (countBound j : ℝ))
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage59KernelData.Cell148
