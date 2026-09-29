import ForestUnimodality.Stage59KernelData.Cell001.Parameters
import ForestUnimodality.FiniteKernelSupportGraphBudget

namespace ForestUnimodality.Stage59KernelData.Cell001
open FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def alpha : ℚ := (979298595200000000000000000000629 / 3920000000000000000000000000000000)
def D : ℚ := (747246585829072315558802045289 / 500000000000000000000000000000)
def mlo : ℚ := (14189189189189189189189189189189 / 500000000000000000000000000000)
def mhi : ℚ := (47297297297297297297297297297297 / 1000000000000000000000000000000)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => Fin.elim0 i) (fun j => (countBound j : ℝ)) alpha 0 D m

theorem budget_lo_positive : 0 < budget mlo := by
  norm_num [budget, RationalRow.graphBudgetWithCounts, KernelBudget.budget,
    row, countBound, alpha, D, mlo]

theorem budget_hi_positive : 0 < budget mhi := by
  norm_num [budget, RationalRow.graphBudgetWithCounts, KernelBudget.budget,
    row, countBound, alpha, D, mhi]

theorem budget_positive {m : ℝ} (hm : m ∈ Set.Icc (mlo : ℝ) (mhi : ℝ)) :
    0 < budget m := by
  have hdM : (0 : ℝ) ≤ row.dM := by norm_num [row]
  have hT : ∀ i ∈ row.terms, (0 : ℝ) ≤ row.price i := by
    intro i _
    exact Fin.elim0 i
  exact KernelBudget.budget_pos_of_endpoints row.terms row.fixedIndices
    row.A row.B row.dδ row.dM alpha 0 D
    (fun i => (row.price i : ℝ)) (fun i => Fin.elim0 i)
    (fun j => (row.fixedPrice j : ℝ)) (fun j => (countBound j : ℝ))
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage59KernelData.Cell001

