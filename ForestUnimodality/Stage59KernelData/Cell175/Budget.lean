import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell175.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell175
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(100810334804378751813471848203/1000000000000000000000000000000)]
def alpha : ℚ := (10872008259586522933403902171/62500000000000000000000000000)
def D : ℚ := (1506473342544662947806884425793/1000000000000000000000000000000)
def mlo : ℚ := (17008977336932638583715236361353/1000000000000000000000000000000)
def mhi : ℚ := (3425419047021156381442651767217/125000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (1192300742736875632327221047354300922936164848855012616760209708594888105937911909183/625000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (63617417925497377062527/6250000000000000000000)) (.exp (-1714680700016269791031126163897745945525172471223813671698659/1000000000000000000000000000000000000000000000000000000000000) (180021192301058173492791/1000000000000000000000000) (22502649037632271686599/125000000000000000000000) { parts := 2, inner := (-1714680700016269791031126163897745945525172471223813671698659/2000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (26518065208947814377614418699/62500000000000000000000000000), innerHi := (84857808668633006008366139837/200000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (56084551534491320871444192203024801712295620952436492143037529628937053096456672087/78125000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (63617417925497377062527/6250000000000000000000)) (.exp (-345317640975498777360435130229414870374394790498337115761051/125000000000000000000000000000000000000000000000000000000000) (63131140062250458314369/1000000000000000000000000) (6313114006225045831437/100000000000000000000000) { parts := 3, inner := (-345317640975498777360435130229414870374394790498337115761051/375000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (398181621403870750838141389743/1000000000000000000000000000000), innerHi := (24886351337741921927383836859/62500000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell175
