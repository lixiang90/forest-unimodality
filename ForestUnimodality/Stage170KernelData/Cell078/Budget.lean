import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell078.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell078
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(74570437960095342362599461211/1000000000000000000000000000000), (175563997214310644938043983069/1000000000000000000000000000000)]
def R : ℚ := (1448970006578947368421052631579/1000000000000000000000000000000)
def D : ℚ := (2271054276835604352514459366729/1000000000000000000000000000000)
def vmax : ℚ := (15656/65025)
def mlo : ℚ := (94131826456310679611650485436892377/1000000000000000000000000000000000)
def mhi : ℚ := (425/4)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (215816045225134336889300962651242708316345325370294893538669862589700105221094540743722574913587/564453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (64399210348407152082472749/10000000000000000000000000)) (.exp (-7019451524830776935196166546156808332867663850871711842393088547/1000000000000000000000000000000000000000000000000000000000000000) (894315868404454117109/1000000000000000000000000) (89431586840445411711/100000000000000000000000) { parts := 8, inner := (-7019451524830776935196166546156808332867663850871711842393088547/8000000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (415849675663571804310188796747/1000000000000000000000000000000), innerHi := (103962418915892951077547199187/250000000000000000000000000000) }))) (.mul (.rat (912738197686373275985261/50000000000000000000000)) (.exp (-16526159717753701223455740024579143815678847129870691958563165013/1000000000000000000000000000000000000000000000000000000000000000) (6493518331263/97656250000000000000) (66493627712133121/1000000000000000000000000) { parts := 17, inner := (-16526159717753701223455740024579143815678847129870691958563165013/17000000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (15131102776512004208545558323/40000000000000000000000000000), innerHi := (94569392353200026303409739519/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (31451732310419782604572483980706520008375595034226598962401/85000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (64399210348407152082472749/10000000000000000000000000)) (.exp (-1267697445321620820164190840587/160000000000000000000000000000) (362274251095806941133/1000000000000000000000000) (181137125547903470567/500000000000000000000000) { parts := 8, inner := (-1267697445321620820164190840587/1280000000000000000000000000000), terms := 40, innerLo := (371432313542127446042681127829/1000000000000000000000000000000), innerHi := (37143231354212744604268112783/100000000000000000000000000000) }))) (.mul (.rat (912738197686373275985261/50000000000000000000000)) (.exp (-2984587952643280963946747712173/160000000000000000000000000000) (1584316716184739/200000000000000000000000) (495098973807731/62500000000000000000000) { parts := 19, inner := (-2984587952643280963946747712173/3040000000000000000000000000000), terms := 40, innerLo := (74929300856056201531628931429/200000000000000000000000000000), innerHi := (187323252140140503829072328573/500000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck = true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mhi := by
  norm_num [budgetExpression_hi, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

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
end ForestUnimodality.Stage170KernelData.Cell078
