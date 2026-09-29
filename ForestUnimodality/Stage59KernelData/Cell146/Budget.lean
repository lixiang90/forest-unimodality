import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell146.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell146
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(49555882676063472966597600707/500000000000000000000000000000)]
def alpha : ℚ := (86369788798232320688628923331/500000000000000000000000000000)
def D : ℚ := (295899713422599019737713604451/200000000000000000000000000000)
def mlo : ℚ := (16298165137614678899082568807339/1000000000000000000000000000000)
def mhi : ℚ := (44100917431192660550458715596329/2000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (857016221642628770235723787790678664936176077672775246034740775307963853236210516361499/625000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1332309904135219014165159/200000000000000000000000)) (.exp (-807669959394740914909730620697092401483934613668115933188673/500000000000000000000000000000000000000000000000000000000000) (99411537626986029779717/500000000000000000000000) (39764615050794411911887/200000000000000000000000) { parts := 2, inner := (-807669959394740914909730620697092401483934613668115933188673/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (222947906053169772509618238219/500000000000000000000000000000), innerHi := (445895812106339545019236476439/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (3978438401371057320106588182171395104723400475630762834761480368942951399000616969030743/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1332309904135219014165159/200000000000000000000000)) (.exp (-2185459890126946005049859326592129465434018597956492137004603/1000000000000000000000000000000000000000000000000000000000000) (1405325226846470378753/12500000000000000000000) (112426018147717630300241/1000000000000000000000000) { parts := 3, inner := (-728486630042315335016619775530709821811339532652164045668201/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (30164928050748476052400189607/62500000000000000000000000000), innerHi := (482638848811975616838403033713/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell146
