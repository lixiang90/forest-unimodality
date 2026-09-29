import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell224.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell224
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(27911280408640169583763237577/250000000000000000000000000000)]
def alpha : ℚ := (45844349370118417737465356513/125000000000000000000000000000)
def D : ℚ := (587751200888888888888888888889/250000000000000000000000000000)
def mlo : ℚ := (3649390243902439024390243902439/250000000000000000000000000000)
def mhi : ℚ := (3073170731707317073170731707317/125000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (911107701156912900246085438644550999345250513814795848018872640795844295316915553553/312500000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (9020896136780685026224091/1000000000000000000000000)) (.exp (-101859154418116716438306693230697489968770520971473566750303/62500000000000000000000000000000000000000000000000000000000) (195979254314097991501863/1000000000000000000000000) (24497406789262248937733/125000000000000000000000) { parts := 2, inner := (-101859154418116716438306693230697489968770520971473566750303/125000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (442695441939600267556194570199/1000000000000000000000000000000), innerHi := (2213477209698001337780972851/5000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (987294509267164588044557149195663512662113194506219568288562706350981992884260589261/625000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (9020896136780685026224091/1000000000000000000000000)) (.exp (-85776130036308813842784583773217469906311562914420700250909/31250000000000000000000000000000000000000000000000000000000) (6425882817384185372601/100000000000000000000000) (64258828173841853726011/1000000000000000000000000) { parts := 3, inner := (-28592043345436271280928194591072489968770520971473566750303/31250000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (400538500081003443279892703749/1000000000000000000000000000000), innerHi := (320430800064802754623914163/800000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell224
