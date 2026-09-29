import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell474.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell474
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(4155418165375743990970569763/25000000000000000000000000000)]
def R : ℚ := (408809575675949367088607594937/500000000000000000000000000000)
def D : ℚ := (163554127/100000000)
def vmax : ℚ := (94098875/376515216)
def mlo : ℚ := (4473872973239584426487564277463/100000000000000000000000000000)
def mhi : ℚ := (4700049244897959183673469387749/100000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (33536759148862789692996426034405887491129826517066534645883614535144262463617632931214410563/570477600000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (2371873497253643492399533/25000000000000000000000)) (.exp (-18590813022583358908937942254854398201424940880594530151269/2500000000000000000000000000000000000000000000000000000000) (294723659061121745157/500000000000000000000000) (117889463624448698063/200000000000000000000000) { parts := 8, inner := (-18590813022583358908937942254854398201424940880594530151269/20000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (39473498980500692459735655921/100000000000000000000000000000), innerHi := (394734989805006924597356559211/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (27428462497738895711424208231497528479372951662009440776286820767580071043151346410178353177/570477600000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (2371873497253643492399533/25000000000000000000000)) (.exp (-19530670010409528424301478130663176509562299031565302033487/2500000000000000000000000000000000000000000000000000000000) (404739056210944095517/1000000000000000000000000) (202369528105472047759/500000000000000000000000) { parts := 8, inner := (-19530670010409528424301478130663176509562299031565302033487/20000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (188307186086647702802259451897/500000000000000000000000000000), innerHi := (75322874434659081120903780759/200000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck = true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mhi := by
  norm_num [budgetExpression_hi, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

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
end ForestUnimodality.Stage170KernelData.Cell474
