import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell085.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell085
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(54196053821580075285822330313/500000000000000000000000000000), (34107539458400355632431972723/200000000000000000000000000000)]
def R : ℚ := (9850373/10000000)
def D : ℚ := (90810693/50000000)
def vmax : ℚ := (5696/23409)
def mlo : ℚ := (17595/256)
def mhi : ℚ := (80937/1024)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (7659901059950512829064298804114172433893/15667200000000000000000000000000000000000)) (.mul (.rat (15388629815663225741673159/1000000000000000000000000)) (.exp (-190715913398140284930808780371447/25600000000000000000000000000000) (581534436804586732799/1000000000000000000000000) (90864755750716677/156250000000000000000) { parts := 8, inner := (-190715913398140284930808780371447/204800000000000000000000000000000), terms := 40, innerLo := (7881373791242161784549910959/20000000000000000000000000000), innerHi := (394068689562108089227495547951/1000000000000000000000000000000) }))) (.mul (.rat (2603751864745239785747799/250000000000000000000000)) (.exp (-120024431354110851470528112012237/10240000000000000000000000000000) (2030090396625210613/250000000000000000000000) (8120361586500842453/1000000000000000000000000) { parts := 12, inner := (-40008143784703617156842704004079/40960000000000000000000000000000), terms := 40, innerLo := (188264290387803368278485574857/500000000000000000000000000000), innerHi := (75305716155121347311394229943/200000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (594698146140704315805739359888686911965031/1253376000000000000000000000000000000000000)) (.mul (.rat (15388629815663225741673159/1000000000000000000000000)) (.exp (-4386466008157226553408601948543281/512000000000000000000000000000000) (190222442198508271439/1000000000000000000000000) (2377780527481353393/12500000000000000000000) { parts := 9, inner := (-487385112017469617045400216504809/512000000000000000000000000000000), terms := 40, innerLo := (385997630974029563901672197161/1000000000000000000000000000000), innerHi := (192998815487014781950836098581/500000000000000000000000000000) }))) (.mul (.rat (2603751864745239785747799/250000000000000000000000)) (.exp (-2760561921144549583822146576281451/204800000000000000000000000000000) (699812471151930197/500000000000000000000000) (279924988460772079/200000000000000000000000) { parts := 14, inner := (-2760561921144549583822146576281451/2867200000000000000000000000000000), terms := 40, innerLo := (381819387534759625700895408111/1000000000000000000000000000000), innerHi := (23863711720922476606305963007/62500000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck = true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mhi := by
  norm_num [budgetExpression_hi, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

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
end ForestUnimodality.Stage170KernelData.Cell085
