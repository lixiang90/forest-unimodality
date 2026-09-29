import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell022.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell022
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(25579687603609833250467363751/200000000000000000000000000000)]
def R : ℚ := (1379818912359550561797752808989/1000000000000000000000000000000)
def D : ℚ := (100571575328707085463842220599/62500000000000000000000000000)
def vmax : ℚ := (3293/15876)
def mlo : ℚ := (391621621621621621621621621621621/4000000000000000000000000000000)
def mhi : ℚ := (9007297297297297297297297297297283/80000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (9352842091767357283831846459925903202747416247476389536247970032094629986827666865652259749127/21168000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (25039286071176750425593127/500000000000000000000000)) (.exp (-10017558739900175237818164885188903018032030188482033493260371/800000000000000000000000000000000000000000000000000000000000) (729150020035232193/200000000000000000000000) (1822875050088080483/500000000000000000000000) { parts := 13, inner := (-10017558739900175237818164885188903018032030188482033493260371/10400000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (381659357723967749178275079833/1000000000000000000000000000000), innerHi := (190829678861983874589137539917/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (3541155863993363363149062072490879232367786465401358329611602952481131615834958761238981893326959/8467200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (25039286071176750425593127/500000000000000000000000)) (.exp (-230403851017704030469817792359344769414736694335086770344988533/16000000000000000000000000000000000000000000000000000000000000) (557256227901999739/1000000000000000000000000) (27862811395099987/50000000000000000000000) { parts := 15, inner := (-230403851017704030469817792359344769414736694335086770344988533/240000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (382886742160726035892181757759/1000000000000000000000000000000), innerHi := (1196521069252268862163067993/3125000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell022
