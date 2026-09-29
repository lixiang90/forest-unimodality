import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell032.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell032
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(111619122497443426932542088359/1000000000000000000000000000000)]
def R : ℚ := (717263696551724137931034482759/500000000000000000000000000000)
def D : ℚ := (824881009467455621301775147929/500000000000000000000000000000)
def vmax : ℚ := (377/1764)
def mlo : ℚ := (98271923076923076923076923076922141/800000000000000000000000000000000)
def mhi : ℚ := (525/4)

def budgetExpression_lo : Expr := (.sub (.rat (1825441212742111743877475622659883083972479900448943306821615299508375983486748071512548438710187/4480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (32860973758664442812005291/1000000000000000000000000)) (.exp (-10969025819982414494328088988593362071548967200448039366185456619/800000000000000000000000000000000000000000000000000000000000000) (1109853786735553699/1000000000000000000000000) (11098537867355537/10000000000000000000000) { parts := 14, inner := (-10969025819982414494328088988593362071548967200448039366185456619/11200000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (375544875840934216411646824591/1000000000000000000000000000000), innerHi := (23471554740058388525727926537/62500000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (1971643251614415225137000019553515503536177753304241062289/5000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (32860973758664442812005291/1000000000000000000000000)) (.exp (-2344001572446311965583383855539/160000000000000000000000000000) (434091789879838457/1000000000000000000000000) (217045894939919229/500000000000000000000000) { parts := 15, inner := (-781333857482103988527794618513/800000000000000000000000000000), terms := 40, innerLo := (94140994127096427786910129341/250000000000000000000000000000), innerHi := (75312795301677142229528103473/200000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell032
