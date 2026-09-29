import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage130KernelData.Cell219.Parameters

namespace ForestUnimodality.Stage130KernelData.Cell219
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(134488613001260786216369100859/1000000000000000000000000000000), (40747148163712392627317446937/200000000000000000000000000000)]
def R : ℚ := (14108033/12500000)
def D : ℚ := (1747598701724137931034482758621/1000000000000000000000000000000)
def vmax : ℚ := (10556/42849)
def mlo : ℚ := (69/2)
def mhi : ℚ := (44003707473682260174411173995509/1000000000000000000000000000000)
def alpha : ℚ := (37231099087/133903125000)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (20068400559137368642523835279254271569397043560038456455884479/62100000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (32045325867076970283164883/5000000000000000000000000)) (.exp (-9279714297086994248929467959271/2000000000000000000000000000000) (241476933556377859573/25000000000000000000000) (9659077342255114382921/1000000000000000000000000) { parts := 5, inner := (-9279714297086994248929467959271/10000000000000000000000000000000), terms := 40, innerLo := (197677451334740621247377987249/500000000000000000000000000000), innerHi := (395354902669481242494755974499/1000000000000000000000000000000) }))) (.mul (.rat (311465258743579997968709/15625000000000000000000)) (.exp (-2811553223296155091284903838653/400000000000000000000000000000) (885920750063802766217/1000000000000000000000000) (442960375031901383109/500000000000000000000000) { parts := 8, inner := (-2811553223296155091284903838653/3200000000000000000000000000000), terms := 40, innerLo := (207679851015907950238810638259/500000000000000000000000000000), innerHi := (415359702031815900477621276519/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (18809903192354695831628162177426991506769017368547242117590942560991446431646574598880946161/71415000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (32045325867076970283164883/5000000000000000000000000)) (.exp (-5917997585048740441413653464977017845230352047244884834042231/1000000000000000000000000000000000000000000000000000000000000) (2690582448907767758051/1000000000000000000000000) (672645612226941939513/250000000000000000000000) { parts := 6, inner := (-1972665861682913480471217821659005948410117349081628278014077/2000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (372941789871919811356530836071/1000000000000000000000000000000), innerHi := (46617723733989976419566354509/125000000000000000000000000000) }))) (.mul (.rat (311465258743579997968709/15625000000000000000000)) (.exp (-1793025588182789395290331208920888615624385655675591383805933/200000000000000000000000000000000000000000000000000000000000) (15973659356090096159/125000000000000000000000) (127789274848720769273/1000000000000000000000000) { parts := 9, inner := (-597675196060929798430110402973629538541461885225197127935311/600000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (369307618868840118840821265421/1000000000000000000000000000000), innerHi := (184653809434420059420410632711/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage130KernelData.Cell219
