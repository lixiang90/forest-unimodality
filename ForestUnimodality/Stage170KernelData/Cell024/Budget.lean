import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell024.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell024
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(25579687603609833250467363751/200000000000000000000000000000)]
def R : ℚ := (1379818912359550561797752808989/1000000000000000000000000000000)
def D : ℚ := (100571575328707085463842220599/62500000000000000000000000000)
def vmax : ℚ := (3293/15876)
def mlo : ℚ := (207167837837837837837837837837837509/1600000000000000000000000000000000)
def mhi : ℚ := (525/4)

def budgetExpression_lo : Expr := (.sub (.rat (5171109444083764490103491700287663923946591107175660582008116151548603544647582828778683747713827/12096000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1069712056507624140522239/10000000000000000000000)) (.exp (-5299288573407192700805809224264929696538943969706995717934736259/320000000000000000000000000000000000000000000000000000000000000) (12852664354544967/200000000000000000000000) (16065830443181209/250000000000000000000000) { parts := 17, inner := (-5299288573407192700805809224264929696538943969706995717934736259/5440000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (9437979261233959079724969301/25000000000000000000000000000), innerHi := (377519170449358363188998772041/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (122215248613198625050639211560732596143696655811109448662759/288000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1069712056507624140522239/10000000000000000000000)) (.exp (-537173439675806498259814638771/32000000000000000000000000000) (25621931053424329/500000000000000000000000) (51243862106848659/1000000000000000000000000) { parts := 17, inner := (-537173439675806498259814638771/544000000000000000000000000000), terms := 40, innerLo := (372524982657459952426566858049/1000000000000000000000000000000), innerHi := (7450499653149199048531337161/20000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell024
