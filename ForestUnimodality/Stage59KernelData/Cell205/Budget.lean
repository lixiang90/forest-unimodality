import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell205.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell205
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(27308240722119234678127301101/1000000000000000000000000000000), (102377016151544926784945071691/1000000000000000000000000000000)]
def alpha : ℚ := (111403432098765432098765432099/500000000000000000000000000000)
def D : ℚ := (1757484967676767676767676767677/1000000000000000000000000000000)
def mlo : ℚ := (81/5)
def mhi : ℚ := (261/10)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.sub (.rat (5087516458475882324627533074155013183868790491309217412453/312500000000000000000000000000000000000000000000000000000)) (.mul (.rat (566697807791849950120877/25000000000000000000000)) (.exp (-2211967498491658008928311389181/5000000000000000000000000000000) (16062419085591844052229/25000000000000000000000) (642496763423673762089161/1000000000000000000000000) { parts := 1, inner := (-2211967498491658008928311389181/5000000000000000000000000000000), terms := 40, innerLo := (642496763423673762089160905207/1000000000000000000000000000000), innerHi := (80312095427959220261145113151/125000000000000000000000000000) }))) (.mul (.rat (3938609748502412521986571/500000000000000000000000)) (.exp (-8292538308275139069580550806971/5000000000000000000000000000000) (95211471812263133657299/500000000000000000000000) (190422943624526267314599/1000000000000000000000000) { parts := 2, inner := (-8292538308275139069580550806971/10000000000000000000000000000000), terms := 40, innerLo := (218187387138055179627753538827/500000000000000000000000000000), innerHi := (87274954855222071851101415531/200000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (927686644354399077009271629002020959374650731179570745771/78125000000000000000000000000000000000000000000000000000)) (.mul (.rat (566697807791849950120877/25000000000000000000000)) (.exp (-7127450828473120250991225587361/10000000000000000000000000000000) (490296444101180279874253/1000000000000000000000000) (245148222050590139937127/500000000000000000000000) { parts := 1, inner := (-7127450828473120250991225587361/10000000000000000000000000000000), terms := 40, innerLo := (12257411102529506996856347573/25000000000000000000000000000), innerHi := (490296444101180279874253902921/1000000000000000000000000000000) }))) (.mul (.rat (3938609748502412521986571/500000000000000000000000)) (.exp (-26720401215553225890870663711351/10000000000000000000000000000000) (69111086370986365757921/1000000000000000000000000) (34555543185493182878961/500000000000000000000000) { parts := 3, inner := (-8906800405184408630290221237117/10000000000000000000000000000000), terms := 40, innerLo := (82075317026949460546306563819/200000000000000000000000000000), innerHi := (51297073141843412841441602387/125000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell205
