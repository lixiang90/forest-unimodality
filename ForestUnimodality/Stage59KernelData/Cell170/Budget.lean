import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell170.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell170
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(50322337138098137558915141073/500000000000000000000000000000)]
def alpha : ℚ := (86679458877625910540666726663/500000000000000000000000000000)
def D : ℚ := (241141887/160000000)
def mlo : ℚ := (2128906536474976165281983048539/125000000000000000000000000000)
def mhi : ℚ := (13719619901727624176261668535029/500000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (592606577811788810080721220023926342435742017976679137674721399718910105153231546011/312500000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1015592790050985705363473/100000000000000000000000)) (.exp (-107131552463994570380482503706855977864708592242369791542347/62500000000000000000000000000000000000000000000000000000000) (180124889266125652564679/1000000000000000000000000) (4503122231653141314117/25000000000000000000000) { parts := 2, inner := (-107131552463994570380482503706855977864708592242369791542347/125000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (212205613301183465986968070463/500000000000000000000000000000), innerHi := (424411226602366931973936140927/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (885945114276660620919557033796233944491356321018214972528659904779954171280807300021/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1015592790050985705363473/100000000000000000000000)) (.exp (-690403338101298342451998357221955154868440027991098777146117/250000000000000000000000000000000000000000000000000000000000) (63189738759909937832307/1000000000000000000000000) (15797434689977484458077/250000000000000000000000) { parts := 3, inner := (-230134446033766114150666119073985051622813342663699592382039/250000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (398304781484568505052246748907/1000000000000000000000000000000), innerHi := (99576195371142126263061687227/250000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell170
