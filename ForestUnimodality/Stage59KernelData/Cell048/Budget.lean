import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell048.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell048
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(9139661641666458664556103613/100000000000000000000000000000)]
def alpha : ℚ := (168186041012825762641560680673/1000000000000000000000000000000)
def D : ℚ := (410707639578947368421052631579/250000000000000000000000000000)
def mlo : ℚ := (8820147091597949632271005125919/500000000000000000000000000000)
def mhi : ℚ := (45657232003565856919991085357699/2000000000000000000000000000000)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha 0 D m

def budgetExpression_lo : Expr := (.sub (.rat (3536938954958077960978730116324917244250309869626332982166815432645736502094197179701051/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (862244630140149181940501/125000000000000000000000)) (.exp (-80613160046933757100172132067767946269134055857881075845347/50000000000000000000000000000000000000000000000000000000000) (24929467471673750309531/125000000000000000000000) (199435739773390002476249/1000000000000000000000000) { parts := 2, inner := (-80613160046933757100172132067767946269134055857881075845347/100000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (446582287796314199584602685407/1000000000000000000000000000000), innerHi := (13955696493634818737018833919/31250000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (35811683817558756123670052571658785882853252143247428340713962343031126826078617000696813/40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (862244630140149181940501/125000000000000000000000)) (.exp (-417291652007657095577361624821392929880109132149343811266487/200000000000000000000000000000000000000000000000000000000000) (124125980166678139705961/1000000000000000000000000) (62062990083339069852981/500000000000000000000000) { parts := 3, inner := (-139097217335885698525787208273797643293369710716447937088829/200000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (99766382699019046178726661897/200000000000000000000000000000), innerHi := (249415956747547615446816654743/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell048
