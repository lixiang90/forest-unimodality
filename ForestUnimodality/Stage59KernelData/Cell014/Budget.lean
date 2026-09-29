import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell014.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell014
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(97321098280359698783095258141/1000000000000000000000000000000)]
def alpha : ℚ := (1086257778500000000000000000000403/3612500000000000000000000000000000)
def D : ℚ := (1167439937688684941432194179447/500000000000000000000000000000)
def mlo : ℚ := (10282258064516129032258064516129/500000000000000000000000000000)
def mhi : ℚ := (4284274193548387096774193548387/125000000000000000000000000000)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha 0 D m

def budgetExpression_lo : Expr := (.sub (.rat (1942403798022805835000567678091312552952053983081032708575386820902143093616652739165281/1062500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (6127551144300520391539067/1000000000000000000000000)) (.exp (-1000680647640795289906826242982053312222636117429071513056189/500000000000000000000000000000000000000000000000000000000000) (4223474290431766482489/31250000000000000000000) (135151177293816527439649/1000000000000000000000000) { parts := 3, inner := (-1000680647640795289906826242982053312222636117429071513056189/1500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (513184201114390105880469570943/1000000000000000000000000000000), innerHi := (4009251571206172702191168523/7812500000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (323557235778965202725487960590919648418443033987350273127722962706429280849958217495843/265625000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (6127551144300520391539067/1000000000000000000000000)) (.exp (-416950269850331370794510934575847436667908352287214539168567/125000000000000000000000000000000000000000000000000000000000) (711862940606510380079/20000000000000000000000) (35593147030325519003951/1000000000000000000000000) { parts := 4, inner := (-416950269850331370794510934575847436667908352287214539168567/500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (108587942883225135556426153239/250000000000000000000000000000), innerHi := (434351771532900542225704612957/1000000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck=true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval = budget mhi := by
  norm_num [budgetExpression_hi, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
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
    row.A row.B row.dδ row.dM alpha 0 D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ))
    (fun j => (row.fixedPrice j : ℝ)) (fun j => (countBound j : ℝ))
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage59KernelData.Cell014
