import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell127.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell127
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(140198746272106266228825658863/1000000000000000000000000000000)]
def alpha : ℚ := (85276734436950175287444181429/500000000000000000000000000000)
def D : ℚ := (293514706932726362270678745391/200000000000000000000000000000)
def mlo : ℚ := (21813500363768643142961076755183/1000000000000000000000000000000)
def mhi : ℚ := (27145689341578755911240451073117/1000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (20855577747284006912405857755714235662943197783665162281772421783654204327547061034521/50000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (3516938526878325976809947/500000000000000000000000)) (.exp (-3058225402806497740130857454251698320597837765946664125136929/1000000000000000000000000000000000000000000000000000000000000) (46970975865279790430141/1000000000000000000000000) (23485487932639895215071/500000000000000000000000) { parts := 4, inner := (-3058225402806497740130857454251698320597837765946664125136929/4000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (465540421847679160681657407411/1000000000000000000000000000000), innerHi := (116385105461919790170414351853/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (3039600616389191030920680338302941971843992493900068993185073421492902120533355821109/12500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (3516938526878325976809947/500000000000000000000000)) (.exp (-3805791612381419409940622609735499762937012015545312912085971/1000000000000000000000000000000000000000000000000000000000000) (4448316696500979780233/200000000000000000000000) (11120791741252449450583/500000000000000000000000) { parts := 4, inner := (-3805791612381419409940622609735499762937012015545312912085971/4000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (96545366280104658336974513769/250000000000000000000000000000), innerHi := (386181465120418633347898055077/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell127
