import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell102.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell102
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(40372537754098325548442729759/500000000000000000000000000000), (114970320366271622228626960681/1000000000000000000000000000000)]
def R : ℚ := (53922541/50000000)
def D : ℚ := (883742337164179104477611940299/500000000000000000000000000000)
def vmax : ℚ := (20/81)
def mlo : ℚ := (4761/64)
def mhi : ℚ := (109503/1280)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (5487988573019445979139011193969571591970389476425905096221813/14400000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (4264171449693848758855097/6250000000000000000000000)) (.exp (-192213652247262127936135836382599/32000000000000000000000000000000) (492451516840680724979/200000000000000000000000) (38472774753178181639/15625000000000000000000) { parts := 7, inner := (-27459093178180303990876548054657/32000000000000000000000000000000), terms := 40, innerLo := (84793653969302698342849202571/200000000000000000000000000000), innerHi := (52996033730814186464280751607/125000000000000000000000000000) }))) (.mul (.rat (20479813476145732664690513/500000000000000000000000)) (.exp (-547373695263819193430492959802241/64000000000000000000000000000000) (193020532540619479187/1000000000000000000000000) (48255133135154869797/250000000000000000000000) { parts := 9, inner := (-60819299473757688158943662200249/64000000000000000000000000000000), terms := 40, innerLo := (19331220881349220291607224853/50000000000000000000000000000), innerHi := (386624417626984405832144497061/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (107826758197768711042511401035049397787193957957795817213101699/288000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (4264171449693848758855097/6250000000000000000000000)) (.exp (-4420914001687028942531124236799777/640000000000000000000000000000000) (1000077154322395975919/1000000000000000000000000) (12500964429029949699/12500000000000000000000) { parts := 7, inner := (-631559143098146991790160605257111/640000000000000000000000000000000), terms := 40, innerLo := (372763480466612478201451685907/1000000000000000000000000000000), innerHi := (93190870116653119550362921477/250000000000000000000000000000) }))) (.mul (.rat (20479813476145732664690513/500000000000000000000000)) (.exp (-12589594991067841448901338075451543/1280000000000000000000000000000000) (26755559690202404173/500000000000000000000000) (53511119380404808347/1000000000000000000000000) { parts := 10, inner := (-12589594991067841448901338075451543/12800000000000000000000000000000000), terms := 40, innerLo := (373976578194448468549025446739/1000000000000000000000000000000), innerHi := (18698828909722423427451272337/50000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell102
