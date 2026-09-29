import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage99KernelData.Cell184.Parameters

namespace ForestUnimodality.Stage99KernelData.Cell184
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(6851342966943315409821627179/50000000000000000000000000000), (143893204145686426703481255277/1000000000000000000000000000000)]
def R : ℚ := (524460776470588235294117647059/250000000000000000000000000000)
def D : ℚ := (278865343/100000000)
def vmax : ℚ := (2/9)
def mlo : ℚ := (5942857142857142857142857142857/250000000000000000000000000000)
def mhi : ℚ := (156/5)
def alpha : ℚ := (174820258823529411764705882353/375000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (5066102281443566273939104149124638699862996693241750476895550437539061051463606716753827/18750000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (21312812344840401657108941/10000000000000000000000000)) (.exp (-40716552489263131578368527235199021236719008097798596910403/12500000000000000000000000000000000000000000000000000000000) (38491255277342452428169/1000000000000000000000000) (3849125527734245242817/100000000000000000000000) { parts := 4, inner := (-40716552489263131578368527235199021236719008097798596910403/50000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (221467765047918175560922913899/500000000000000000000000000000), innerHi := (442935530095836351121845827799/1000000000000000000000000000000) }))) (.mul (.rat (20050511966802542218601957/5000000000000000000000000)) (.exp (-855136756065793621552117174217579443827979187653328074106389/250000000000000000000000000000000000000000000000000000000000) (32694545336869970289087/1000000000000000000000000) (510852270888593285767/15625000000000000000000) { parts := 4, inner := (-855136756065793621552117174217579443827979187653328074106389/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (212612517501451249759744700699/500000000000000000000000000000), innerHi := (425225035002902499519489401399/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (32593770264918906071216119773550039288403044373208390241/156250000000000000000000000000000000000000000000000000000)) (.mul (.rat (21312812344840401657108941/10000000000000000000000000)) (.exp (-267202375710789300983043459981/62500000000000000000000000000) (6954368943574694566819/500000000000000000000000) (13908737887149389133639/1000000000000000000000000) { parts := 5, inner := (-267202375710789300983043459981/312500000000000000000000000000), terms := 40, innerLo := (106315736779223563257438910919/250000000000000000000000000000), innerHi := (425262947116894253029755643677/1000000000000000000000000000000) }))) (.mul (.rat (20050511966802542218601957/5000000000000000000000000)) (.exp (-5611834961681770641435768955803/1250000000000000000000000000000) (2245323024876071387189/200000000000000000000000) (5613307562190178467973/500000000000000000000000) { parts := 5, inner := (-5611834961681770641435768955803/6250000000000000000000000000000), terms := 40, innerLo := (203713481581064446685246822209/500000000000000000000000000000), innerHi := (407426963162128893370493644419/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage99KernelData.Cell184
