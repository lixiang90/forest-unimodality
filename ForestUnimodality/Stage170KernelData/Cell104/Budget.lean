import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell104.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell104
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(40372537754098325548442729759/500000000000000000000000000000), (179298536061889179706434124893/1000000000000000000000000000000)]
def R : ℚ := (53922541/50000000)
def D : ℚ := (883742337164179104477611940299/500000000000000000000000000000)
def vmax : ℚ := (20/81)
def mlo : ℚ := (2518569/25600)
def mhi : ℚ := (1575/16)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (46070051823570301888709187035894904757287513037327780877006858947/115200000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (5182524914848472441519789/500000000000000000000000)) (.exp (-101681022038801665678215857446394871/12800000000000000000000000000000000) (354844871110359474043/1000000000000000000000000) (88711217777589868511/250000000000000000000000) { parts := 8, inner := (-101681022038801665678215857446394871/102400000000000000000000000000000000), terms := 40, innerLo := (592754417447120016532009689/1600000000000000000000000000), innerHi := (185235755452225005166253027813/500000000000000000000000000000) }))) (.mul (.rat (35849696020336949686679873/1000000000000000000000000)) (.exp (-451575734670856169444054087497638117/25600000000000000000000000000000000) (2183662708316761/100000000000000000000000) (21836627083167611/1000000000000000000000000) { parts := 18, inner := (-50175081630095129938228231944182013/51200000000000000000000000000000000), terms := 40, innerLo := (375317830834004318189680203323/1000000000000000000000000000000), innerHi := (93829457708501079547420050831/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (1151527257028835371821507564598511953077598966953714667039669/2880000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (5182524914848472441519789/500000000000000000000000)) (.exp (-2543469878508194509551891974817/320000000000000000000000000000) (70649375885003755759/200000000000000000000000) (88311719856254694699/250000000000000000000000) { parts := 8, inner := (-2543469878508194509551891974817/2560000000000000000000000000000), terms := 40, innerLo := (370262553369469610814265930377/1000000000000000000000000000000), innerHi := (185131276684734805407132965189/500000000000000000000000000000) }))) (.mul (.rat (35849696020336949686679873/1000000000000000000000000)) (.exp (-11295807771899018321505349868259/640000000000000000000000000000) (2161886241024413/100000000000000000000000) (21618862410244131/1000000000000000000000000) { parts := 18, inner := (-1255089752433224257945038874251/1280000000000000000000000000000), terms := 40, innerLo := (93777227445821486914061576143/250000000000000000000000000000), innerHi := (375108909783285947656246304573/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell104
