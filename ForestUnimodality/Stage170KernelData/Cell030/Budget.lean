import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell030.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell030
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(111619122497443426932542088359/1000000000000000000000000000000)]
def R : ℚ := (717263696551724137931034482759/500000000000000000000000000000)
def D : ℚ := (824881009467455621301775147929/500000000000000000000000000000)
def vmax : ℚ := (377/1764)
def mlo : ℚ := (185769230769230769230769230769229/2000000000000000000000000000000)
def mhi : ℚ := (4272692307692307692307692307692267/40000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (508259739891942254907220238811537372845322219894147727915365476171736915088516692518482451/1200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (5057295034008252088142399/500000000000000000000000)) (.exp (-20735398525486605849391472568229417904629427600090811656305211/2000000000000000000000000000000000000000000000000000000000000) (3143152264473480251/100000000000000000000000) (31431522644734802511/1000000000000000000000000) { parts := 11, inner := (-20735398525486605849391472568229417904629427600090811656305211/22000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (194822713527290734759897879709/500000000000000000000000000000), innerHi := (389645427054581469519795759419/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (966977831452546830237819499602827344452374148079112633551455891572301541094567470988811990259/2400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (5057295034008252088142399/500000000000000000000000)) (.exp (-476914166086191934536003869069276611806476834802088668095019853/40000000000000000000000000000000000000000000000000000000000000) (1659243946479150227/250000000000000000000000) (6636975785916600909/1000000000000000000000000) { parts := 12, inner := (-476914166086191934536003869069276611806476834802088668095019853/480000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (185126045309041362076836721413/500000000000000000000000000000), innerHi := (370252090618082724153673442827/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell030
