import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage80KernelData.Cell083.Parameters

namespace ForestUnimodality.Stage80KernelData.Cell083
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(23939368855369197288494469047/250000000000000000000000000000), (280065252093933762142925341949/1000000000000000000000000000000)]
def R : ℚ := (187418723169/250000000000)
def D : ℚ := (1619335743149367088607594936709/1000000000000000000000000000000)
def vmax : ℚ := (1/4)
def mlo : ℚ := (23/1)
def mhi : ℚ := (189/8)
def alpha : ℚ := (-249998405774920926436077951229/1000000000000000000000000000000)
def varianceIntercept : ℚ := (952346438482564309307640414539/100000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (4028518799821436408051861490148677526120127217095931984353/5000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1971983571458973405476911/312500000000000000000000)) (.exp (-550605483673491537635372788081/250000000000000000000000000000) (55267562529745589190781/500000000000000000000000) (110535125059491178381563/1000000000000000000000000) { parts := 3, inner := (-550605483673491537635372788081/750000000000000000000000000000), terms := 40, innerLo := (4799177015435139398184497453/10000000000000000000000000000), innerHi := (479917701543513939818449745301/1000000000000000000000000000000) }))) (.mul (.rat (15320988744439835826938179/500000000000000000000000)) (.exp (-6441500798160476529287282864827/1000000000000000000000000000000) (1594012593372844352027/1000000000000000000000000) (398503148343211088007/250000000000000000000000) { parts := 7, inner := (-6441500798160476529287282864827/7000000000000000000000000000000), terms := 40, innerLo := (398433607865589203911637848961/1000000000000000000000000000000), innerHi := (199216803932794601955818924481/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (31737912037298457215801023326591548882310912661364374490879/40000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1971983571458973405476911/312500000000000000000000)) (.exp (-4524540713664778287525454649883/2000000000000000000000000000000) (13014230081707962114089/125000000000000000000000) (104113840653663696912713/1000000000000000000000000) { parts := 3, inner := (-1508180237888259429175151549961/2000000000000000000000000000000), terms := 40, innerLo := (235219231550492687732022007713/500000000000000000000000000000), innerHi := (470438463100985375464044015427/1000000000000000000000000000000) }))) (.mul (.rat (15320988744439835826938179/500000000000000000000000)) (.exp (-52932332645753481045012889628361/8000000000000000000000000000000) (669025246232926235059/500000000000000000000000) (1338050492465852470119/1000000000000000000000000) { parts := 7, inner := (-7561761806536211577858984232623/8000000000000000000000000000000), terms := 40, innerLo := (388593983050362845963350690833/1000000000000000000000000000000), innerHi := (194296991525181422981675345417/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage80KernelData.Cell083
