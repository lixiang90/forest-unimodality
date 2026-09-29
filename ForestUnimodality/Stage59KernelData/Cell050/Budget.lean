import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell050.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell050
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(22955188320621994893367190557/250000000000000000000000000000)]
def alpha : ℚ := (42325798755605825696215798113/250000000000000000000000000000)
def D : ℚ := (820519872206819701359482950747/500000000000000000000000000000)
def mlo : ℚ := (17591287920880097788643182575841/1000000000000000000000000000000)
def mhi : ℚ := (4553039226580731192354706078453/200000000000000000000000000000)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha 0 D m

def budgetExpression_lo : Expr := (.sub (.rat (3577653727866410318076639114435258048119043619080788973886169276412249604573729585113037/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1403586851850691097354229/200000000000000000000000)) (.exp (-403811327026085596132859177012464825375786045664288751533437/250000000000000000000000000000000000000000000000000000000000) (19884188693122217374517/100000000000000000000000) (198841886931222173745171/1000000000000000000000000) { parts := 2, inner := (-403811327026085596132859177012464825375786045664288751533437/500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (445916905859401313801502994891/1000000000000000000000000000000), innerHi := (111479226464850328450375748723/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (2258387175488800787712018529816590155388035313100617085834875988871049851730038546336717/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1403586851850691097354229/200000000000000000000000)) (.exp (-104515872877339801352034139932638764986261822007047442768321/50000000000000000000000000000000000000000000000000000000000) (30911969158659905601701/250000000000000000000000) (24729575326927924481361/200000000000000000000000) { parts := 3, inner := (-104515872877339801352034139932638764986261822007047442768321/150000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (124547657274536362981679489479/250000000000000000000000000000), innerHi := (498190629098145451926717957917/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell050
