import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell015.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell015
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(24568660801978636143221469313/200000000000000000000000000000)]
def R : ℚ := (332518930693069306930693069307/250000000000000000000000000000)
def D : ℚ := (1557844460223537146614069690993/1000000000000000000000000000000)
def vmax : ℚ := (3939/19600)
def mlo : ℚ := (1091910256410256410256410256410247363/8000000000000000000000000000000000)
def mhi : ℚ := (1225/8)

def budgetExpression_lo : Expr := (.sub (.rat (712650985360765267758500001685619808765927957821168737442962797949961848940744816483285281846733467/1568000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (5505252065382265413973073/6250000000000000000000)) (.exp (-26826772715945108483102939998959995669744016601335572238643671619/1600000000000000000000000000000000000000000000000000000000000000) (6534470691173001/125000000000000000000000) (52275765529384009/1000000000000000000000000) { parts := 17, inner := (-26826772715945108483102939998959995669744016601335572238643671619/27200000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (11655066375649873595331369253/31250000000000000000000000000), innerHi := (372962124020795955050603816097/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (138956406810021637276459943298430838326048374338455495371277/320000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (5505252065382265413973073/6250000000000000000000)) (.exp (-1203864379296953171017851996337/64000000000000000000000000000) (6772598983888301/1000000000000000000000000) (3386299491944151/500000000000000000000000) { parts := 19, inner := (-1203864379296953171017851996337/1216000000000000000000000000000), terms := 40, innerLo := (371569241443358803849874834121/1000000000000000000000000000000), innerHi := (185784620721679401924937417061/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell015
