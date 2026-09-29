import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell025.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell025
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(118952202164032185701210973187/1000000000000000000000000000000)]
def alpha : ℚ := (53922541/202500000)
def D : ℚ := (883742337164179104477611940299/500000000000000000000000000000)
def mlo : ℚ := (18/1)
def mhi : ℚ := (225/8)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha 0 D m

def budgetExpression_lo : Expr := (.sub (.rat (622220465477136639982442673893645777622581246052638869439/562500000000000000000000000000000000000000000000000000000)) (.mul (.rat (1145173080528781861531229/125000000000000000000000)) (.exp (-1070569819476289671310898758683/500000000000000000000000000000) (117520835354394654928749/1000000000000000000000000) (94016668283515723943/800000000000000000000) { parts := 3, inner := (-356856606492096557103632919561/500000000000000000000000000000), terms := 40, innerLo := (489822003035044293051758853967/1000000000000000000000000000000), innerHi := (30613875189690268315734928373/62500000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (126855774166591353585903474806563159670579523236654707019/360000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1145173080528781861531229/125000000000000000000000)) (.exp (-1070569819476289671310898758683/320000000000000000000000000000) (8810377006033507677279/250000000000000000000000) (35241508024134030709117/1000000000000000000000000) { parts := 4, inner := (-1070569819476289671310898758683/1280000000000000000000000000000), terms := 40, innerLo := (17330999604521260806471832309/40000000000000000000000000000), innerHi := (216637495056515760080897903863/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell025
