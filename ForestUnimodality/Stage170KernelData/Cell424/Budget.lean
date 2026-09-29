import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell424.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell424
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(119984313105215384271646889291/1000000000000000000000000000000)]
def R : ℚ := (524460776470588235294117647059/250000000000000000000000000000)
def D : ℚ := (278865343/100000000)
def vmax : ℚ := (2/9)
def mlo : ℚ := (2667191719342714767115332512859/62500000000000000000000000000)
def mhi : ℚ := (296354635482523863012814723651/6250000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (105157488150184324205358959608174546993180106751142169783136699564449835609620110485967/390625000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (77178051656338615416075299/10000000000000000000000000)) (.exp (-320021166365254044564086458848623445125114201405261606892969/62500000000000000000000000000000000000000000000000000000000) (2986999693367004584287/500000000000000000000000) (238959975469360366743/40000000000000000000000) { parts := 6, inner := (-106673722121751348188028819616207815041704733801753868964323/125000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (106492135876541264573338793017/250000000000000000000000000000), innerHi := (425968543506165058293355172069/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (1490124419218061979183283721720660797155156196519916988251993627919272629336839400633/5859375000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (77178051656338615416075299/10000000000000000000000000)) (.exp (-35557907373917116062676273205402605013901577933917956321441/6250000000000000000000000000000000000000000000000000000000) (3382077275115225360619/1000000000000000000000000) (169103863755761268031/50000000000000000000000) { parts := 6, inner := (-35557907373917116062676273205402605013901577933917956321441/37500000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (19371678768075606899705009521/50000000000000000000000000000), innerHi := (387433575361512137994100190421/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell424
