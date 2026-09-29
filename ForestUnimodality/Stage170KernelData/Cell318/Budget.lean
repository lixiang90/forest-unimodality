import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell318.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell318
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(28454796869942295217164016983/250000000000000000000000000000)]
def R : ℚ := (43935559/25000000)
def D : ℚ := (2300991799491525423728813559323/1000000000000000000000000000000)
def vmax : ℚ := (31860/137641)
def mlo : ℚ := (557692046532779443658464306299153/10000000000000000000000000000000)
def mhi : ℚ := (12826917070253927204144679044880519/200000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (229273457089650155096161921196980824286751659220940707399845742872783917473269209644737714273829/688205000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (479210959912722174180999/40000000000000000000000)) (.exp (-15869013900072645367378682518620089754096151640983575970515399/2500000000000000000000000000000000000000000000000000000000000) (1750934628772340310481/1000000000000000000000000) (875467314386170155241/500000000000000000000000) { parts := 7, inner := (-15869013900072645367378682518620089754096151640983575970515399/17500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (201907021964559701977085237441/500000000000000000000000000000), innerHi := (403814043929119403954170474883/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (88163342087667936594808087717131468702300779575968426940936618149816182615008142175534208312491731/275282000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (479210959912722174180999/40000000000000000000000)) (.exp (-364987319701670843449709697928262064344211487742622247321854177/50000000000000000000000000000000000000000000000000000000000000) (168927529395924879301/250000000000000000000000) (135142023516739903441/200000000000000000000000) { parts := 8, inner := (-364987319701670843449709697928262064344211487742622247321854177/400000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (200765949486540358939235341017/500000000000000000000000000000), innerHi := (80306379794616143575694136407/200000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell318
