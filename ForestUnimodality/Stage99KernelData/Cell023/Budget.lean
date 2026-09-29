import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage99KernelData.Cell023.Parameters

namespace ForestUnimodality.Stage99KernelData.Cell023
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(143167501845527608968723616789/1000000000000000000000000000000), (232179493237273661517595972203/1000000000000000000000000000000)]
def R : ℚ := (1030670341379310344827586206897/1000000000000000000000000000000)
def D : ℚ := (358219917476923076923076923077/200000000000000000000000000000)
def vmax : ℚ := (638/2601)
def mlo : ℚ := (3622159090909090909090909090909/125000000000000000000000000000)
def mhi : ℚ := (153/4)
def alpha : ℚ := (328783838900000000000000000000143/1300500000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (4214619196195998606703190777329028570434350363381384201428346406119514261615239916736805581/10837500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1834637884927490603104161/400000000000000000000000)) (.exp (-518575468332521879077052873312415962045286770217366479671201/125000000000000000000000000000000000000000000000000000000000) (1578644297772554846821/100000000000000000000000) (15786442977725548468211/1000000000000000000000000) { parts := 5, inner := (-518575468332521879077052873312415962045286770217366479671201/625000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (43617107037935488409917657943/100000000000000000000000000000), innerHi := (436171070379354884099176579431/1000000000000000000000000000000) }))) (.mul (.rat (510242521030111584323663/31250000000000000000000)) (.exp (-840991062152056586462883137951186279136978429667134764002527/125000000000000000000000000000000000000000000000000000000000) (1197010001204029293613/1000000000000000000000000) (598505000602014646807/500000000000000000000000) { parts := 7, inner := (-840991062152056586462883137951186279136978429667134764002527/875000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (15298378029797134244837066803/40000000000000000000000000000), innerHi := (95614862686232089030231667519/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (433035279804235584146948560676400910384595468117887790013087/1360000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1834637884927490603104161/400000000000000000000000)) (.exp (-21904627782365724172214713368717/4000000000000000000000000000000) (418538348681425841249/100000000000000000000000) (4185383486814258412491/1000000000000000000000000) { parts := 6, inner := (-7301542594121908057404904456239/8000000000000000000000000000000), terms := 40, innerLo := (200720877569586812731105931701/500000000000000000000000000000), innerHi := (401441755139173625462211863403/1000000000000000000000000000000) }))) (.mul (.rat (510242521030111584323663/31250000000000000000000)) (.exp (-35523462465302870212192183747059/4000000000000000000000000000000) (69511886107580397641/500000000000000000000000) (139023772215160795283/1000000000000000000000000) { parts := 9, inner := (-3947051385033652245799131527451/4000000000000000000000000000000), terms := 40, innerLo := (1491125963627175085642874177/4000000000000000000000000000), innerHi := (372781490906793771410718544251/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage99KernelData.Cell023
