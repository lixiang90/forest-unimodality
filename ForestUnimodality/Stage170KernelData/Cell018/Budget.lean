import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell018.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell018
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(104249861087605159830651630899/1000000000000000000000000000000)]
def R : ℚ := (8458603/6250000)
def D : ℚ := (63356039/40000000)
def vmax : ℚ := (10/49)
def mlo : ℚ := (3703/32)
def mhi : ℚ := (85169/640)

def budgetExpression_lo : Expr := (.sub (.rat (4057322017526240127092670179712404594569/8960000000000000000000000000000000000000)) (.mul (.rat (13479375145591147244772401/500000000000000000000000)) (.exp (-386037235607401906852902989218997/32000000000000000000000000000000) (2882620466550395401/500000000000000000000000) (5765240933100790803/1000000000000000000000000) { parts := 13, inner := (-386037235607401906852902989218997/416000000000000000000000000000000), terms := 40, innerLo := (197676918723700427398116184571/500000000000000000000000000000), innerHi := (395353837447400854796232369143/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (76988676261627810955313551538247380487587/179200000000000000000000000000000000000000)) (.mul (.rat (13479375145591147244772401/500000000000000000000000)) (.exp (-8878856418970243857616768752036931/640000000000000000000000000000000) (471965316901814123/500000000000000000000000) (943930633803628247/1000000000000000000000000) { parts := 14, inner := (-1268408059852891979659538393148133/1280000000000000000000000000000000), terms := 40, innerLo := (92806540896072580890019487307/250000000000000000000000000000), innerHi := (371226163584290323560077949229/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell018
