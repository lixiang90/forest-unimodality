import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell016.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell016
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(8036235215179068192668115761/62500000000000000000000000000)]
def alpha : ℚ := (305611967308823529411764705882507/956250000000000000000000000000000)
def D : ℚ := (18476581956786703601108033241/8000000000000000000000000000)
def mlo : ℚ := (19716494845360824742268041237113/1000000000000000000000000000000)
def mhi : ℚ := (6572164948453608247422680412371/200000000000000000000000000000)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha 0 D m

def budgetExpression_lo : Expr := (.sub (.rat (12754589463399645584235827832900159434455936418386254840222985786083983546330394686329837/6375000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1262732225493578397390593/100000000000000000000000)) (.exp (-158446390196185236272966715390847284400274309446809133437993/62500000000000000000000000000000000000000000000000000000000) (15850089126160246717151/200000000000000000000000) (19812611407700308396439/250000000000000000000000) { parts := 3, inner := (-52815463398728412090988905130282428133424769815603044479331/62500000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (214768495748957431412143943801/500000000000000000000000000000), innerHi := (429536991497914862824287887603/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (2265612596712204651605896872400878125381163544964113129424503041879486334470344019408767/1912500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1262732225493578397390593/100000000000000000000000)) (.exp (-52815463398728412090988905130282428133424769815603044479331/12500000000000000000000000000000000000000000000000000000000) (7310933932346861602737/500000000000000000000000) (584874714587748928219/40000000000000000000000) { parts := 5, inner := (-52815463398728412090988905130282428133424769815603044479331/62500000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (214768495748957431412143943801/500000000000000000000000000000), innerHi := (429536991497914862824287887603/1000000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck=true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval = budget mhi := by
  norm_num [budgetExpression_hi, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
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
    row.A row.B row.dδ row.dM alpha 0 D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ))
    (fun j => (row.fixedPrice j : ℝ)) (fun j => (countBound j : ℝ))
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage59KernelData.Cell016
