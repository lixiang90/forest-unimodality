import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell552.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell552
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(58388493209979575014980350259/500000000000000000000000000000)]
def R : ℚ := (1967611776744186046511627906977/1000000000000000000000000000000)
def D : ℚ := (566455824682926829268292682927/200000000000000000000000000000)
def vmax : ℚ := (902/3969)
def mlo : ℚ := (40688817608243152393193031535457/1000000000000000000000000000000)
def mhi : ℚ := (2154113873377578656110219316583/50000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (3012574168261279229363193655182826920591763144965760789301035809935795083562974222697476259/11025000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (87923623182861998515136293/10000000000000000000000000)) (.exp (-2375758750641002675048830945035765019566203990574178437633363/500000000000000000000000000000000000000000000000000000000000) (8638576201127098459953/1000000000000000000000000) (4319288100563549229977/500000000000000000000000) { parts := 5, inner := (-2375758750641002675048830945035765019566203990574178437633363/2500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (386623665264743140164578046111/1000000000000000000000000000000), innerHi := (12081989539523223130143063941/31250000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (38934779944149993647288705677304333837479316679239861061993231448254339313036801891935221/147000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (87923623182861998515136293/10000000000000000000000000)) (.exp (-125775463269229553384938108854833588297742388096720947044997/25000000000000000000000000000000000000000000000000000000000) (6532153981335039043559/1000000000000000000000000) (163303849533375976089/25000000000000000000000) { parts := 6, inner := (-41925154423076517794979369618277862765914129365573649014999/50000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (432357239810725862292998172239/1000000000000000000000000000000), innerHi := (5404465497634073278662477153/12500000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck = true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mhi := by
  norm_num [budgetExpression_hi, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_hi_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mhi := by
  rw [← budgetExpression_hi_eval]
  exact budgetExpression_hi.positiveCheck_sound budgetExpression_hi_checked

theorem budget_positive {m : ℝ} (hm : m ∈ Set.Icc (mlo : ℝ) (mhi : ℝ)) :
    0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D m := by
  have hs := row.signCheck_sound row_checked
  have hdM : (0 : ℝ) ≤ row.dM := by norm_num [row]
  have hT : ∀ i ∈ row.terms, (0 : ℝ) ≤ row.price i := by
    intro i hi
    exact hs.price i hi
  exact KernelBudget.budget_pos_of_endpoints row.terms (∅ : Finset ℤ)
    row.A row.B row.dδ row.dM (R * vmax : ℚ) 0 D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ)) (fun _ => 0) (fun _ => 0)
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage170KernelData.Cell552
