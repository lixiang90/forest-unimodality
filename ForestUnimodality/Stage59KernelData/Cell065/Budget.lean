import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell065.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell065
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(11678828403853685031638690021/125000000000000000000000000000), (58992594354553598191109416461/250000000000000000000000000000)]
def alpha : ℚ := (55507775195763/300125000000000)
def D : ℚ := (1632339656356627543878539894477/1000000000000000000000000000000)
def mlo : ℚ := (22458333333333333333333333333333/1000000000000000000000000000000)
def mhi : ℚ := (441/16)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.sub (.rat (993612745321839512755094751601097917619766381716171171597498253741762130249763750971933079/1200500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (6311953003488651070540527/1000000000000000000000000)) (.exp (-262287021236547343002218913388287773723865382104989453769993/125000000000000000000000000000000000000000000000000000000000) (61332625525539011324183/500000000000000000000000) (122665251051078022648367/1000000000000000000000000) { parts := 3, inner := (-87429007078849114334072971129429257907955127368329817923331/125000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (31054213514143983867699280847/62500000000000000000000000000), innerHi := (496867416226303741883188493553/1000000000000000000000000000000) }))) (.mul (.rat (7341667439391426519534889/1000000000000000000000000)) (.exp (-1324875348212682892708665644686605335801881815467269630194513/250000000000000000000000000000000000000000000000000000000000) (624260421487423975301/125000000000000000000000) (4994083371899391802409/1000000000000000000000000) { parts := 6, inner := (-441625116070894297569555214895535111933960605155756543398171/500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (8268739188873382731852278893/20000000000000000000000000000), innerHi := (413436959443669136592613944651/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (1992653665229110266518339257949802168456616031310177955785539/3920000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (6311953003488651070540527/1000000000000000000000000)) (.exp (-5150363326099475098952662299261/2000000000000000000000000000000) (76139989719429284668987/1000000000000000000000000) (19034997429857321167247/250000000000000000000000) { parts := 3, inner := (-1716787775366491699650887433087/2000000000000000000000000000000), terms := 40, innerLo := (211921137118116651864788310367/500000000000000000000000000000), innerHi := (84768454847246660745915324147/200000000000000000000000000000) }))) (.mul (.rat (7341667439391426519534889/1000000000000000000000000)) (.exp (-26015734110358136802279252659301/4000000000000000000000000000000) (1497536989283563289917/1000000000000000000000000) (748768494641781644959/500000000000000000000000) { parts := 7, inner := (-3716533444336876686039893237043/4000000000000000000000000000000), terms := 40, innerLo := (394895794181535409897059833987/1000000000000000000000000000000), innerHi := (98723948545383852474264958497/250000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell065
