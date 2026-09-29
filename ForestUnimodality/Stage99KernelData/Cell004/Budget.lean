import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage99KernelData.Cell004.Parameters

namespace ForestUnimodality.Stage99KernelData.Cell004
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(104249861087605159830651630899/1000000000000000000000000000000), (179929245891556516040624553247/1000000000000000000000000000000)]
def R : ℚ := (8458603/6250000)
def D : ℚ := (63356039/40000000)
def vmax : ℚ := (10/49)
def mlo : ℚ := (175/4)
def mhi : ℚ := (231/4)
def alpha : ℚ := (8458603/30625000)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (954206246741060713130408765157544363/2240000000000000000000000000000000000)) (.mul (.rat (9343755571279280247587451/25000000000000000000000000)) (.exp (-729749027613236118814561416293/160000000000000000000000000000) (5226159441112863950649/500000000000000000000000) (10452318882225727901299/1000000000000000000000000) { parts := 5, inner := (-729749027613236118814561416293/800000000000000000000000000000), terms := 40, innerLo := (401645152855101774008595689077/1000000000000000000000000000000), innerHi := (200822576427550887004297844539/500000000000000000000000000000) }))) (.mul (.rat (48267193434005672969533407/10000000000000000000000000)) (.exp (-1259504721240895612284371872729/160000000000000000000000000000) (190653733601312544607/500000000000000000000000) (76261493440525017843/200000000000000000000000) { parts := 8, inner := (-1259504721240895612284371872729/1280000000000000000000000000000), terms := 40, innerLo := (23363582187539777329275044877/62500000000000000000000000000), innerHi := (373817315000636437268400718033/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (22897591653750064081450813917958963979/56000000000000000000000000000000000000)) (.mul (.rat (9343755571279280247587451/25000000000000000000000000)) (.exp (-24081717911236791920880526737669/4000000000000000000000000000000) (60715658247387433559/25000000000000000000000) (2428626329895497342361/1000000000000000000000000) { parts := 7, inner := (-3440245415890970274411503819667/4000000000000000000000000000000), terms := 40, innerLo := (423136120439324939650279335391/1000000000000000000000000000000), innerHi := (13223003763728904364071229231/31250000000000000000000000000) }))) (.mul (.rat (48267193434005672969533407/10000000000000000000000000)) (.exp (-41563655800949555205384271800057/4000000000000000000000000000000) (7677563518325071557/250000000000000000000000) (30710254073300286229/1000000000000000000000000) { parts := 11, inner := (-3778514163722686836853115618187/4000000000000000000000000000000), terms := 40, innerLo := (97205994068027222669733482133/250000000000000000000000000000), innerHi := (388823976272108890678933928533/1000000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck = true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mhi := by
  norm_num [budgetExpression_hi, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_hi_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mhi := by
  rw [← budgetExpression_hi_eval]
  exact budgetExpression_hi.positiveCheck_sound budgetExpression_hi_checked

theorem budget_positive {m : ℝ} (hm : m ∈ Set.Icc (mlo : ℝ) (mhi : ℝ)) :
    0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D m := by
  have hs := row.signCheck_sound row_checked
  have hdM : (0 : ℝ) ≤ row.dM := by norm_num [row]
  have hT : ∀ i ∈ row.terms, (0 : ℝ) ≤ row.price i := by
    intro i hi
    exact hs.price i hi
  exact KernelBudget.budget_pos_of_endpoints row.terms (∅ : Finset ℤ)
    row.A row.B row.dδ row.dM alpha varianceIntercept D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ)) (fun _ => 0) (fun _ => 0)
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage99KernelData.Cell004
