import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell149.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell149
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(142559498125635256304721225959/1000000000000000000000000000000)]
def alpha : ℚ := (21484602083265338483172242211/125000000000000000000000000000)
def D : ℚ := (1487592200669724770642201834863/1000000000000000000000000000000)
def mlo : ℚ := (44052803840279293039493781365917/2000000000000000000000000000000)
def mhi : ℚ := (5554483962469997818023128954833/200000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (2039389999318230034182727020090266215529201517917713888386565458062064938802421051581293/4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (4349137823093506938221253/500000000000000000000000)) (.exp (-6280145606497273496920224131303950561937372432330937818239403/2000000000000000000000000000000000000000000000000000000000000) (2704977930523247168027/62500000000000000000000) (43279646888371954688433/1000000000000000000000000) { parts := 4, inner := (-6280145606497273496920224131303950561937372432330937818239403/8000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (456111400112173759976204290337/1000000000000000000000000000000), innerHi := (228055700056086879988102145169/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (14966722056378517096744304456576155147340942218967523220385531026874801581595268717643/50000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (4349137823093506938221253/500000000000000000000000)) (.exp (-791844446036612745263854346990496254859519233181862098109847/200000000000000000000000000000000000000000000000000000000000) (19077946773905263813751/1000000000000000000000000) (2384743346738157976719/125000000000000000000000) { parts := 4, inner := (-791844446036612745263854346990496254859519233181862098109847/800000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (74329789666100145901485141281/200000000000000000000000000000), innerHi := (185824474165250364753712853203/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell149
