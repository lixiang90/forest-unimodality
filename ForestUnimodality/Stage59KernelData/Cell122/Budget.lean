import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell122.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell122
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(12258374817780617061578183751/125000000000000000000000000000)]
def alpha : ℚ := (176537869869176453954189838817/1000000000000000000000000000000)
def D : ℚ := (1477242057571150458885695744879/1000000000000000000000000000000)
def mlo : ℚ := (4129716981132075471698113207547/250000000000000000000000000000)
def mhi : ℚ := (43726415094339622641509433962263/2000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (340113519705492236440829848615760194363894088545112670481809256947501608525698035084537/312500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (673753064386612088298989/125000000000000000000000)) (.exp (-50623618646070425648168395632075748577861131593329165968797/31250000000000000000000000000000000000000000000000000000000) (49476861764404601357627/250000000000000000000000) (197907447057618405430509/1000000000000000000000000) { parts := 2, inner := (-50623618646070425648168395632075748577861131593329165968797/62500000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (444867898434600926454835913431/1000000000000000000000000000000), innerHi := (55608487304325115806854489179/125000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (816538526585542949911937559138683446680485383141642683315082992113591952683314746482031/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (673753064386612088298989/125000000000000000000000)) (.exp (-536014785664275095098253600810221740361058780799231013788513/250000000000000000000000000000000000000000000000000000000000) (11717823319769939315159/100000000000000000000000) (117178233197699393151591/1000000000000000000000000) { parts := 3, inner := (-178671595221425031699417866936740580120352926933077004596171/250000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (244672777926696263915228115577/500000000000000000000000000000), innerHi := (97869111170678505566091246231/200000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell122
