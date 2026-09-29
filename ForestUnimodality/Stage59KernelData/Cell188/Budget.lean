import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell188.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell188
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(101444833110264849252830581293/1000000000000000000000000000000)]
def alpha : ℚ := (189632760718145288073170389353/1000000000000000000000000000000)
def D : ℚ := (1512608840330637173984813469793/1000000000000000000000000000000)
def mlo : ℚ := (845607453518571958609885806159/50000000000000000000000000000)
def mhi : ℚ := (13623675640021437110937049099229/500000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (930343396139439356018093435259991768653765440135204400624746641881872389496280388081/500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1003431339041758363350709/100000000000000000000000)) (.exp (-85782506998987573128958057485417461236952369578529889583587/50000000000000000000000000000000000000000000000000000000000) (179846757128842782135769/1000000000000000000000000) (17984675712884278213577/100000000000000000000000) { parts := 2, inner := (-85782506998987573128958057485417461236952369578529889583587/100000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (424083431801859929883454813739/1000000000000000000000000000000), innerHi := (21204171590092996494172740687/50000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (3442685360673617049189644106060647403622344579907008599672146913034635022206256810211/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1003431339041758363350709/100000000000000000000000)) (.exp (-1382051501650355344855435370598460060928528353109150108123097/500000000000000000000000000000000000000000000000000000000000) (2521304561768920927579/40000000000000000000000) (15758153511055755797369/250000000000000000000000) { parts := 3, inner := (-460683833883451781618478456866153353642842784369716702707699/500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (79594874397122328765051601449/200000000000000000000000000000), innerHi := (198987185992805821912629003623/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell188
