import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell118.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell118
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(97444714122472307943307455513/1000000000000000000000000000000)]
def alpha : ℚ := (43625670979391076841172299393/250000000000000000000000000000)
def D : ℚ := (2311663243198169879854708019/1562500000000000000000000000)
def mlo : ℚ := (2074451774763055194201821222821/125000000000000000000000000000)
def mhi : ℚ := (10982391748745586322244935885523/500000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (43745589659234123294614532605908497728990387021049926033112604974257798792651561314323/39062500000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (5548640022441907682093643/1000000000000000000000000)) (.exp (-202144360152641227737532500575317270674946966736799717862173/125000000000000000000000000000000000000000000000000000000000) (39692509222846271352823/200000000000000000000000) (49615636528557839191029/250000000000000000000000) { parts := 2, inner := (-202144360152641227737532500575317270674946966736799717862173/250000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (445491353579652942700459538391/1000000000000000000000000000000), innerHi := (55686419197456617837557442299/125000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (104888195979914473379124140508505252221154563530579702350880081540184042340243251275373/156250000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (5548640022441907682093643/1000000000000000000000000)) (.exp (-1070176024337512382139877944222273635615255851683524583238299/500000000000000000000000000000000000000000000000000000000000) (58806715040148220698389/500000000000000000000000) (117613430080296441396779/1000000000000000000000000) { parts := 3, inner := (-356725341445837460713292648074091211871751950561174861079433/500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (244975306466031969961819485993/500000000000000000000000000000), innerHi := (489950612932063939923638971987/1000000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck=true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval = budget mhi := by
  norm_num [budgetExpression_hi, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
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
    row.A row.B row.dδ row.dM alpha varianceIntercept D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ))
    (fun j => (row.fixedPrice j : ℝ)) (fun j => (countBound j : ℝ))
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage59KernelData.Cell118
