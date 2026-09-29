import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell126.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell126
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(97719315156794242671909294063/1000000000000000000000000000000)]
def alpha : ℚ := (85276734436950175287444181429/500000000000000000000000000000)
def D : ℚ := (293514706932726362270678745391/200000000000000000000000000000)
def mlo : ℚ := (16481311385958530374681702437249/1000000000000000000000000000000)
def mhi : ℚ := (21813500363768643142961076755183/1000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (57574549421458515512123749921584882231376756649076942726972547092298493555020542808733/125000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (2143249582877871706187989/1000000000000000000000000)) (.exp (-1610542461521742943621872817305876563998335093193002145752687/1000000000000000000000000000000000000000000000000000000000000) (199779212140433202804709/1000000000000000000000000) (19977921214043320280471/100000000000000000000000) { parts := 2, inner := (-1610542461521742943621872817305876563998335093193002145752687/2000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (1396770871889487104126670287/3125000000000000000000000000), innerHi := (446966679004635873320534491841/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (71677597823854001998299969904080892034269122849644389933977322805143385069972615136709/250000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (2143249582877871706187989/1000000000000000000000000)) (.exp (-2131600316719953895970125787610767841420080726347368206378529/1000000000000000000000000000000000000000000000000000000000000) (118647268634924694646247/1000000000000000000000000) (14830908579365586830781/125000000000000000000000) { parts := 3, inner := (-710533438906651298656708595870255947140026908782456068792843/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (491382005255789087776656791461/1000000000000000000000000000000), innerHi := (245691002627894543888328395731/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell126
