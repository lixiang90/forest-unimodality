import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell031.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell031
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(66757626791333463979629227261/500000000000000000000000000000)]
def R : ℚ := (717263696551724137931034482759/500000000000000000000000000000)
def D : ℚ := (824881009467455621301775147929/500000000000000000000000000000)
def vmax : ℚ := (377/1764)
def mlo : ℚ := (4272692307692307692307692307692267/40000000000000000000000000000000)
def mhi : ℚ := (98271923076923076923076923076922141/800000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (1505727161946392578652154130148755406903296580686639974499544845264507879426327092241911622127/3600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (4703578054797684160348581/25000000000000000000000)) (.exp (-285234798471124404365269648324016129631955952661350367395290687/20000000000000000000000000000000000000000000000000000000000000) (320018476385052213/500000000000000000000000) (640036952770104427/1000000000000000000000000) { parts := 15, inner := (-285234798471124404365269648324016129631955952661350367395290687/300000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (386438454537717422912233841541/1000000000000000000000000000000), innerHi := (193219227268858711456116920771/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (572114089867569846234731271417733803272546738784431574974522644312714892551814266614301236860003/1440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (4703578054797684160348581/25000000000000000000000)) (.exp (-6560400364835861300401201911452370981534986911211058450091685801/400000000000000000000000000000000000000000000000000000000000000) (75359117885363453/1000000000000000000000000) (37679558942681727/500000000000000000000000) { parts := 17, inner := (-6560400364835861300401201911452370981534986911211058450091685801/6800000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (381072832946786297362329931751/1000000000000000000000000000000), innerHi := (47634104118348287170291241469/125000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell031
