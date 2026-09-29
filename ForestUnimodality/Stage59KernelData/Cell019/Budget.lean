import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell019.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell019
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(107406005451657970098750314547/1000000000000000000000000000000)]
def alpha : ℚ := (945211434291666666666666666666701/2709375000000000000000000000000000)
def D : ℚ := (2271054276835604352514459366729/1000000000000000000000000000000)
def mlo : ℚ := (9283980582524271844660194174757/500000000000000000000000000000)
def mhi : ℚ := (7736650485436893203883495145631/250000000000000000000000000000)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha 0 D m

def budgetExpression_lo : Expr := (.sub (.rat (124185733157175249139476391160414637027932455867854027805290246934205232564712803214556779/54187500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (595977517952681701274287/50000000000000000000000)) (.exp (-997155269059688678708058138694811992483901960377350837290079/500000000000000000000000000000000000000000000000000000000000) (8506716420727505964833/62500000000000000000000) (136107462731640095437329/1000000000000000000000000) { parts := 2, inner := (-997155269059688678708058138694811992483901960377350837290079/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (46115931142956188727619760587/125000000000000000000000000000), innerHi := (368927449143649509820958084697/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (29768112282376461862204021480164734293055716029002919959611533819396217420496682877972967/27093750000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (595977517952681701274287/50000000000000000000000)) (.exp (-830962724216407232256715115579027894737493576642808822794157/250000000000000000000000000000000000000000000000000000000000) (9003469661580156610933/250000000000000000000000) (36013878646320626443733/1000000000000000000000000) { parts := 4, inner := (-830962724216407232256715115579027894737493576642808822794157/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (108907423280680358821838813943/250000000000000000000000000000), innerHi := (435629693122721435287355255773/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell019
