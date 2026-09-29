import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell145.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell145
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(28449107038358667245861109721/200000000000000000000000000000)]
def alpha : ℚ := (172249507970063157156463434673/1000000000000000000000000000000)
def D : ℚ := (740014235023605339934576960481/500000000000000000000000000000)
def mlo : ℚ := (22074800194286218925243961672627/1000000000000000000000000000000)
def mhi : ℚ := (6958360930807612487305161831589/250000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (121753021150171987003414991254103512736892930139674388055516128004181538371270518570103/250000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (4219985165141082461559563/500000000000000000000000)) (.exp (-628008353577629346001185713807551702107694465695465529307067/200000000000000000000000000000000000000000000000000000000000) (34624792086926856887/800000000000000000000) (43280990108658571108751/1000000000000000000000000) { parts := 4, inner := (-628008353577629346001185713807551702107694465695465529307067/800000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (456114939021334179503736155051/1000000000000000000000000000000), innerHi := (114028734755333544875934038763/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (8835794310358116984645696462873572311094297831759593216318408565511870096581373552651/31250000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (4219985165141082461559563/500000000000000000000000)) (.exp (-197959154932078815587330279352381973985416644548964452776669/50000000000000000000000000000000000000000000000000000000000) (1907869333797794779981/100000000000000000000000) (19078693337977947799811/1000000000000000000000000) { parts := 4, inner := (-197959154932078815587330279352381973985416644548964452776669/200000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (371652584147345177467507454439/1000000000000000000000000000000), innerHi := (9291314603683629436687686361/25000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell145
