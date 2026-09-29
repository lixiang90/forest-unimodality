import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage80KernelData.Cell010.Parameters

namespace ForestUnimodality.Stage80KernelData.Cell010
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(29810624092422477535348571433/250000000000000000000000000000), (200698444220169535879115172691/1000000000000000000000000000000)]
def R : ℚ := (3803687/2500000)
def D : ℚ := (3383039/2000000)
def vmax : ℚ := (2/9)
def mlo : ℚ := (30/1)
def mhi : ℚ := (75/2)
def alpha : ℚ := (3803687/11250000)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (11098156914178883558681515384121969/30000000000000000000000000000000000)) (.mul (.rat (1619398666514820089856741/6250000000000000000000000)) (.exp (-89431872277267432606045714299/25000000000000000000000000000) (13975883084257382247283/500000000000000000000000) (27951766168514764494567/1000000000000000000000000) { parts := 4, inner := (-89431872277267432606045714299/100000000000000000000000000000), terms := 40, innerLo := (408886068539544214873351303283/1000000000000000000000000000000), innerHi := (102221517134886053718337825821/250000000000000000000000000000) }))) (.mul (.rat (3995047862533000482265777/625000000000000000000000)) (.exp (-602095332660508607637345518073/100000000000000000000000000000) (1213677215043798429753/500000000000000000000000) (2427354430087596859507/1000000000000000000000000) { parts := 7, inner := (-602095332660508607637345518073/700000000000000000000000000000), terms := 40, innerLo := (423104456003125358334549468227/1000000000000000000000000000000), innerHi := (105776114000781339583637367057/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (8486054466001529986110961381121969/24000000000000000000000000000000000)) (.mul (.rat (1619398666514820089856741/6250000000000000000000000)) (.exp (-89431872277267432606045714299/20000000000000000000000000000) (2857271944345160296461/250000000000000000000000) (2285817555476128237169/200000000000000000000000) { parts := 5, inner := (-89431872277267432606045714299/100000000000000000000000000000), terms := 40, innerLo := (408886068539544214873351303283/1000000000000000000000000000000), innerHi := (102221517134886053718337825821/250000000000000000000000000000) }))) (.mul (.rat (3995047862533000482265777/625000000000000000000000)) (.exp (-602095332660508607637345518073/80000000000000000000000000000) (538786236622308357403/1000000000000000000000000) (134696559155577089351/250000000000000000000000) { parts := 8, inner := (-602095332660508607637345518073/640000000000000000000000000000), terms := 40, innerLo := (390325623065564123892584267789/1000000000000000000000000000000), innerHi := (39032562306556412389258426779/100000000000000000000000000000) })))
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
end ForestUnimodality.Stage80KernelData.Cell010
