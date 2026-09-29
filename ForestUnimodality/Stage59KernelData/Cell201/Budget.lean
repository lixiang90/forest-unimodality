import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell201.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell201
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(26966784789376477831236396619/1000000000000000000000000000000), (101408824195483108086449858499/1000000000000000000000000000000)]
def alpha : ℚ := (24321005758605371900826446281/125000000000000000000000000000)
def D : ℚ := (1596711461442597603401623502127/1000000000000000000000000000000)
def mlo : ℚ := (33/2)
def mhi : ℚ := (26583333333333333333333333333333/1000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.sub (.rat (64405469154270118878255699884861496268895166618893992017/2500000000000000000000000000000000000000000000000000000)) (.mul (.rat (3985849065988036699081931/100000000000000000000000)) (.exp (-889903898049423768430801088427/2000000000000000000000000000000) (320427534501790327578713/500000000000000000000000) (640855069003580655157427/1000000000000000000000000) { parts := 1, inner := (-889903898049423768430801088427/2000000000000000000000000000000), terms := 40, innerLo := (640855069003580655157426158117/1000000000000000000000000000000), innerHi := (320427534501790327578713079059/500000000000000000000000000000) }))) (.mul (.rat (2757458416853443838867577/10000000000000000000000000)) (.exp (-3346491198450942566852845330467/2000000000000000000000000000000) (187637081525754689391389/1000000000000000000000000) (18763708152575468939139/100000000000000000000000) { parts := 2, inner := (-3346491198450942566852845330467/4000000000000000000000000000000), terms := 40, innerLo := (54146370135401662229682732183/125000000000000000000000000000), innerHi := (86634192216642659567492371493/200000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (12279769157435488757746540372800152749256703545899497151169920066589039876745030590271/625000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (3985849065988036699081931/100000000000000000000000)) (.exp (-716867028984258035680367543455074344405070207840722921201127/1000000000000000000000000000000000000000000000000000000000000) (97655925605324268614043/200000000000000000000000) (61034953503327667883777/125000000000000000000000) { parts := 1, inner := (-716867028984258035680367543455074344405070207840722921201127/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (15258738375831916970944227539/31250000000000000000000000000), innerHi := (488279628026621343070215281249/1000000000000000000000000000000) }))) (.mul (.rat (2757458416853443838867577/10000000000000000000000000)) (.exp (-2695784576529925956631458738431716197058601505630637850047167/1000000000000000000000000000000000000000000000000000000000000) (67489410389479020886141/1000000000000000000000000) (33744705194739510443071/500000000000000000000000) { parts := 3, inner := (-898594858843308652210486246143905399019533835210212616682389/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (50892668632574478801686495293/125000000000000000000000000000), innerHi := (81428269812119166082698392469/200000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell201
