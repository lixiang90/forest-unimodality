import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell204.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell204
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(101622396095723485155817803377/1000000000000000000000000000000)]
def alpha : ℚ := (44087567758809025935520114853/200000000000000000000000000000)
def D : ℚ := (352187893061224489795918367347/200000000000000000000000000000)
def mlo : ℚ := (16272727272727272727272727272727/1000000000000000000000000000000)
def mhi : ℚ := (26217171717171717171717171717171/1000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (1105985962297156820558035482692428042093430196457225287553518417196598073681214801573539/500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (216671051266835092974361/20000000000000000000000)) (.exp (-1653673536466773076626489709498426830255610257231321140599079/1000000000000000000000000000000000000000000000000000000000000) (1494888285445048514783/7812500000000000000000) (7653828021478648395689/40000000000000000000000) { parts := 2, inner := (-1653673536466773076626489709498426830255610257231321140599079/2000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (27339424696260970469095513039/62500000000000000000000000000), innerHi := (3499446361121404220044225669/8000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (446795414203977387133666485337281075576012849771700873988384849662633716126954241981761/500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (216671051266835092974361/20000000000000000000000)) (.exp (-2664251808752023290120455643080770553635123269015696332686467/1000000000000000000000000000000000000000000000000000000000000) (348257233229113985719/5000000000000000000000) (69651446645822797143801/1000000000000000000000000) { parts := 3, inner := (-888083936250674430040151881026923517878374423005232110895489/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (8228866993112505511930747791/20000000000000000000000000000), innerHi := (411443349655625275596537389551/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell204
