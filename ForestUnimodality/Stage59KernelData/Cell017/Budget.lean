import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell017.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell017
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(6460752661446166348280518249/62500000000000000000000000000)]
def alpha : ℚ := (594669462750000000000000000000363/1806250000000000000000000000000000)
def D : ℚ := (2296765958762886597938144329897/1000000000000000000000000000000)
def mlo : ℚ := (19318181818181818181818181818181/1000000000000000000000000000000)
def mhi : ℚ := (32196969696969696969696969696969/1000000000000000000000000000000)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha 0 D m

def budgetExpression_lo : Expr := (.sub (.rat (3845225236455041706261922660212849081107196674743806222239083091738140123253586340377135799/1445000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (61181917973191977111469/5000000000000000000000)) (.exp (-124809994596119122637237284355676532111458816772987770485069/62500000000000000000000000000000000000000000000000000000000) (16968417528263104759969/125000000000000000000000) (135747340226104838079753/1000000000000000000000000) { parts := 2, inner := (-124809994596119122637237284355676532111458816772987770485069/125000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (46054882379970183732299966743/125000000000000000000000000000), innerHi := (73687811807952293971679946789/200000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (2078975033414785429864381560192264444487375269468522879587934123647036545226855816403958317/1445000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (61181917973191977111469/5000000000000000000000)) (.exp (-208016657660198537728728807259465194020872325399211804487281/62500000000000000000000000000000000000000000000000000000000) (17927602708455192376431/500000000000000000000000) (35855205416910384752863/1000000000000000000000000) { parts := 4, inner := (-208016657660198537728728807259465194020872325399211804487281/250000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (87029812807880846082278866683/200000000000000000000000000000), innerHi := (54393633004925528801424291677/125000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell017
