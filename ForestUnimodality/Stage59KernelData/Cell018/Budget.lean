import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell018.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell018
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(52694512008699157917809651633/500000000000000000000000000000)]
def alpha : ℚ := (3673764590166666666666666666667441/10837500000000000000000000000000000)
def D : ℚ := (2283914681359044995408631772269/1000000000000000000000000000000)
def mlo : ℚ := (18935643564356435643564356435643/1000000000000000000000000000000)
def mhi : ℚ := (6311881188118811881188118811881/200000000000000000000000000000)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha 0 D m

def budgetExpression_lo : Expr := (.sub (.rat (23494710780114091657906340221410486083383965677609793678474086424976073553659523049805269/9031250000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1193780815826844943217111/100000000000000000000000)) (.exp (-997804497194427123938722363842668281315004991564343414355019/500000000000000000000000000000000000000000000000000000000000) (13593084783151000983171/100000000000000000000000) (135930847831510009831711/1000000000000000000000000) { parts := 2, inner := (-997804497194427123938722363842668281315004991564343414355019/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (4608600109976286392984979481/12500000000000000000000000000), innerHi := (368688008798102911438798358481/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (61026892845934804829570679775584000746035059038397755054523837822321564698605495686031079/43350000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1193780815826844943217111/100000000000000000000000)) (.exp (-332601499064809041312907454614222760438334997188114471451673/100000000000000000000000000000000000000000000000000000000000) (898400637664794044879/25000000000000000000000) (35936025506591761795161/1000000000000000000000000) { parts := 4, inner := (-332601499064809041312907454614222760438334997188114471451673/400000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (87078814197886472608757064941/200000000000000000000000000000), innerHi := (217697035494716181521892662353/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell018
