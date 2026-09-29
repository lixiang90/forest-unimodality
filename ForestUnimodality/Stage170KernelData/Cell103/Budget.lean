import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell103.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell103
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(40372537754098325548442729759/500000000000000000000000000000), (179298536061889179706434124893/1000000000000000000000000000000)]
def R : ℚ := (53922541/50000000)
def D : ℚ := (883742337164179104477611940299/500000000000000000000000000000)
def vmax : ℚ := (20/81)
def mlo : ℚ := (109503/1280)
def mhi : ℚ := (2518569/25600)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (24992955741330695156925446273103427617077070577166688331730731/64000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (98434330429739080869921963/10000000000000000000000000)) (.exp (-4420914001687028942531124236799777/640000000000000000000000000000000) (1000077154322395975919/1000000000000000000000000) (12500964429029949699/12500000000000000000000) { parts := 7, inner := (-631559143098146991790160605257111/640000000000000000000000000000000), terms := 40, innerLo := (372763480466612478201451685907/1000000000000000000000000000000), innerHi := (93190870116653119550362921477/250000000000000000000000000000) }))) (.mul (.rat (3461397916382935591173009/100000000000000000000000)) (.exp (-19633727594385050845393655978158179/1280000000000000000000000000000000) (217982798526276347/1000000000000000000000000) (54495699631569087/250000000000000000000000) { parts := 16, inner := (-19633727594385050845393655978158179/20480000000000000000000000000000000), terms := 40, innerLo := (383399364774208604794574966903/1000000000000000000000000000000), innerHi := (47924920596776075599321870863/125000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (491720759400752147500837205309125184470116373274833831629806813/1280000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (98434330429739080869921963/10000000000000000000000000)) (.exp (-101681022038801665678215857446394871/12800000000000000000000000000000000) (354844871110359474043/1000000000000000000000000) (88711217777589868511/250000000000000000000000) { parts := 8, inner := (-101681022038801665678215857446394871/102400000000000000000000000000000000), terms := 40, innerLo := (592754417447120016532009689/1600000000000000000000000000), innerHi := (185235755452225005166253027813/500000000000000000000000000000) }))) (.mul (.rat (3461397916382935591173009/100000000000000000000000)) (.exp (-451575734670856169444054087497638117/25600000000000000000000000000000000) (2183662708316761/100000000000000000000000) (21836627083167611/1000000000000000000000000) { parts := 18, inner := (-50175081630095129938228231944182013/51200000000000000000000000000000000), terms := 40, innerLo := (375317830834004318189680203323/1000000000000000000000000000000), innerHi := (93829457708501079547420050831/250000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell103
