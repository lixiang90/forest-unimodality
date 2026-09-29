import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell090.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell090
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(110036660823938018485890235639/1000000000000000000000000000000)]
def R : ℚ := (503797271022727272727272727273/500000000000000000000000000000)
def D : ℚ := (5771073659/3200000000)
def vmax : ℚ := (5720/23409)
def mlo : ℚ := (31129615384615384615384615384614937/400000000000000000000000000000000)
def mhi : ℚ := (715981153846153846153846153846143551/8000000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (222337461210883740148037098354513776714795214737684142558891330849209251712312519120267232911480689/468180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (3638373510362434615217353/100000000000000000000000)) (.exp (-3425398929656565923920191539197544207436205038820802354209139743/400000000000000000000000000000000000000000000000000000000000000) (4773757734203696337/25000000000000000000000) (190950309368147853481/1000000000000000000000000) { parts := 9, inner := (-3425398929656565923920191539197544207436205038820802354209139743/3600000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (386161461598100422302844369213/1000000000000000000000000000000), innerHi := (193080730799050211151422184607/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (86481845485812769341813795733163630905731885242137288964986123675928401872206689723108369770401284481/187272000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (3638373510362434615217353/100000000000000000000000)) (.exp (-78784175382101016250164405401543516771032715892878454146810214089/8000000000000000000000000000000000000000000000000000000000000000) (6606454287470239343/125000000000000000000000) (10570326859952382949/200000000000000000000000) { parts := 10, inner := (-78784175382101016250164405401543516771032715892878454146810214089/80000000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (186756551703261379892066216431/500000000000000000000000000000), innerHi := (373513103406522759784132432863/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell090
