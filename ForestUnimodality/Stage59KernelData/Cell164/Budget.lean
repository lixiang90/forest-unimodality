import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell164.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell164
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(20039346364942857034551143617/200000000000000000000000000000)]
def alpha : ℚ := (43393560675583311772927522517/250000000000000000000000000000)
def D : ℚ := (750041043071528632678184828289/500000000000000000000000000000)
def mlo : ℚ := (17071834450004240522432363667203/1000000000000000000000000000000)
def mhi : ℚ := (6876155542362819099313035365957/250000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (2132675205959193474962614283088592241771492639510893949880122713628315402091990341469/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (2298862428859929085689373/250000000000000000000000)) (.exp (-342108403628598716301665499384293875759631726205303645693251/200000000000000000000000000000000000000000000000000000000000) (22595973329873150585533/125000000000000000000000) (36153557327797040936853/200000000000000000000000) { parts := 2, inner := (-342108403628598716301665499384293875759631726205303645693251/400000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (106291987773945479510957590029/250000000000000000000000000000), innerHi := (425167951095781918043830360117/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (196344393975970405912706697511279312570685068512805386420116612804230773556718597211/312500000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (2298862428859929085689373/250000000000000000000000)) (.exp (-137793662572630038510393048363123098137743390118380459646469/50000000000000000000000000000000000000000000000000000000000) (15888374311498502305683/250000000000000000000000) (63553497245994009222733/1000000000000000000000000) { parts := 3, inner := (-137793662572630038510393048363123098137743390118380459646469/150000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (4988345178248833002341321547/12500000000000000000000000000), innerHi := (399067614259906640187305723761/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell164
