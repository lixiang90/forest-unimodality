import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage99KernelData.Cell182.Parameters

namespace ForestUnimodality.Stage99KernelData.Cell182
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(35384138187026258969862619781/200000000000000000000000000000)]
def R : ℚ := (1967611776744186046511627906977/1000000000000000000000000000000)
def D : ℚ := (2334529135219512195121951219513/1000000000000000000000000000000)
def vmax : ℚ := (902/3969)
def mlo : ℚ := (12144578313253012048192771084337/500000000000000000000000000000)
def mhi : ℚ := (15560240963855421686746987951807/500000000000000000000000000000)
def alpha : ℚ := (887392911311627906976744186046627/1984500000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.rat (10351233060890785806406224895396503205746804918706864162302553501415934801109014068499278843/39690000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (70005066335862604631756767/10000000000000000000000000)) (.exp (-429725437259306855923150852280084022409549111307106915470197/100000000000000000000000000000000000000000000000000000000000) (13605864409622726218737/1000000000000000000000000) (6802932204811363109369/500000000000000000000000) { parts := 5, inner := (-429725437259306855923150852280084022409549111307106915470197/500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (42339451521147767625278327843/100000000000000000000000000000), innerHi := (423394515211477676252783278431/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (8058952482015280791614186556119538359340095205785057070150876222332971940656660725892994233/39690000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (70005066335862604631756767/10000000000000000000000000)) (.exp (-550585716488486909151537029483865393992463210856380392894267/100000000000000000000000000000000000000000000000000000000000) (4062904508805653581039/1000000000000000000000000) (50786306360070669763/12500000000000000000000) { parts := 6, inner := (-550585716488486909151537029483865393992463210856380392894267/600000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (399459513909791628606642757857/1000000000000000000000000000000), innerHi := (199729756954895814303321378929/500000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck = true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mhi := by
  norm_num [budgetExpression_hi, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]

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
end ForestUnimodality.Stage99KernelData.Cell182
