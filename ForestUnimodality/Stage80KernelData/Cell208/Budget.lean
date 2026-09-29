import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage80KernelData.Cell208.Parameters

namespace ForestUnimodality.Stage80KernelData.Cell208
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(185951625158499333235772893883/1000000000000000000000000000000)]
def R : ℚ := (408539117/400000000)
def D : ℚ := (2051068320476190476190476190477/1000000000000000000000000000000)
def vmax : ℚ := (336/1369)
def mlo : ℚ := (17898113207547169811320754716981/800000000000000000000000000000)
def mhi : ℚ := (47377358490566037735849056603773/2000000000000000000000000000000)
def alpha : ℚ := (-6563388382587244891027864493/31250000000000000000000000000)
def varianceIntercept : ℚ := (5074133183396184001484732339147/500000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (8942346499032393361615165204552545938862924930735067525532326083209923937246342863027909/32000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (16889897111714311961350177/1000000000000000000000000)) (.exp (-3328183238214197500140644662970047138464601707635233011127223/800000000000000000000000000000000000000000000000000000000000) (975248965816171432217/62500000000000000000000) (15603983453058742915473/1000000000000000000000000) { parts := 5, inner := (-3328183238214197500140644662970047138464601707635233011127223/4000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (108789531102588534275763337119/250000000000000000000000000000), innerHi := (435158124410354137103053348477/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (13067183626906668078698315225778796111741564681765549665183963118834986647305419151977863/40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (16889897111714311961350177/1000000000000000000000000)) (.exp (-8809896807037581618019353519626551613200378990956031906420559/2000000000000000000000000000000000000000000000000000000000000) (12216736739209578383149/1000000000000000000000000) (244334734784191567663/20000000000000000000000) { parts := 5, inner := (-8809896807037581618019353519626551613200378990956031906420559/10000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (20718630605195923568833631673/50000000000000000000000000000), innerHi := (414372612103918471376672633461/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage80KernelData.Cell208
