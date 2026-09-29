import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage130KernelData.Cell025.Parameters

namespace ForestUnimodality.Stage130KernelData.Cell025
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(114970320366271622228626960681/1000000000000000000000000000000), (232597286932437569959880637399/1000000000000000000000000000000)]
def R : ℚ := (53922541/50000000)
def D : ℚ := (883742337164179104477611940299/500000000000000000000000000000)
def vmax : ℚ := (20/81)
def mlo : ℚ := (297/8)
def mhi : ℚ := (765/16)
def alpha : ℚ := (53922541/202500000)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (402163163523171449679942415995845564370946952016186256065937/1200000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (25883197974974652133539621/5000000000000000000000000)) (.exp (-34146185148782671801902207322257/8000000000000000000000000000000) (7002974272082552843877/500000000000000000000000) (2801189708833021137551/200000000000000000000000) { parts := 5, inner := (-34146185148782671801902207322257/40000000000000000000000000000000), terms := 40, innerLo := (425855739932636573962824618417/1000000000000000000000000000000), innerHi := (212927869966318286981412309209/500000000000000000000000000000) }))) (.mul (.rat (4941594376315924819209613/200000000000000000000000)) (.exp (-69081394218933958278084549307503/8000000000000000000000000000000) (177742572322940612213/1000000000000000000000000) (88871286161470306107/500000000000000000000000) { parts := 9, inner := (-7675710468770439808676061034167/8000000000000000000000000000000), terms := 40, innerLo := (95774561225008221422372427799/250000000000000000000000000000), innerHi := (383098244900032885689489711197/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (402948131865051102256246292627218713118736198570469668465539/1440000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (25883197974974652133539621/5000000000000000000000000)) (.exp (-17590459016039558200979924984193/3200000000000000000000000000000) (1024743641392254844923/250000000000000000000000) (4098974565569019379693/1000000000000000000000000) { parts := 6, inner := (-5863486338679852733659974994731/6400000000000000000000000000000), terms := 40, innerLo := (100012099877518942540101064037/250000000000000000000000000000), innerHi := (400048399510075770160404256149/1000000000000000000000000000000) }))) (.mul (.rat (4941594376315924819209613/200000000000000000000000)) (.exp (-35587384900662948203861737522047/3200000000000000000000000000000) (14797419041979677177/1000000000000000000000000) (7398709520989838589/500000000000000000000000) { parts := 12, inner := (-11862461633554316067953912507349/12800000000000000000000000000000), terms := 40, innerLo := (395836189922398508992623539851/1000000000000000000000000000000), innerHi := (98959047480599627248155884963/250000000000000000000000000000) })))
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
end ForestUnimodality.Stage130KernelData.Cell025
