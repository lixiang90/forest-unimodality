import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell357.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell357
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(28540061780381397000539871871/250000000000000000000000000000), (78377520495425705032001394177/500000000000000000000000000000)]
def R : ℚ := (365708962790697674418604651163/250000000000000000000000000000)
def D : ℚ := (6663680383/4000000000)
def vmax : ℚ := (860/3969)
def mlo : ℚ := (567/8)
def mhi : ℚ := (315/4)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (64298922118475336882187395401215792195076974859241957/156250000000000000000000000000000000000000000000000000)) (.mul (.rat (9303768962305364320641843/5000000000000000000000000)) (.exp (-16182215029476252099306107350857/2000000000000000000000000000000) (61250078483791976243/200000000000000000000000) (299072648846640509/976562500000000000000) { parts := 9, inner := (-1798023892164028011034011927873/2000000000000000000000000000000), terms := 40, innerLo := (101742892752036039955213191461/250000000000000000000000000000), innerHi := (81394314201628831964170553169/200000000000000000000000000000) }))) (.mul (.rat (34015766732455570142690249/5000000000000000000000000)) (.exp (-44440054120906374753144790498359/4000000000000000000000000000000) (14961751248156928933/1000000000000000000000000) (7480875624078464467/500000000000000000000000) { parts := 12, inner := (-14813351373635458251048263499453/16000000000000000000000000000000), terms := 40, innerLo := (198100333574030524382856714469/500000000000000000000000000000), innerHi := (396200667148061048765713428939/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (6203206583893553620465343400850691320286330539915773/15625000000000000000000000000000000000000000000000000)) (.mul (.rat (9303768962305364320641843/5000000000000000000000000)) (.exp (-1798023892164028011034011927873/200000000000000000000000000000) (24927040664920949037/200000000000000000000000) (62317601662302372593/500000000000000000000000) { parts := 9, inner := (-199780432462669779003779103097/200000000000000000000000000000), terms := 40, innerLo := (184141767430079303318000766393/500000000000000000000000000000), innerHi := (368283534860158606636001532787/1000000000000000000000000000000) }))) (.mul (.rat (34015766732455570142690249/5000000000000000000000000)) (.exp (-4937783791211819417016087833151/400000000000000000000000000000) (4353808938143001097/1000000000000000000000000) (2176904469071500549/500000000000000000000000) { parts := 13, inner := (-4937783791211819417016087833151/5200000000000000000000000000000), terms := 40, innerLo := (77381177057287692412436303583/200000000000000000000000000000), innerHi := (96726471321609615515545379479/250000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell357
