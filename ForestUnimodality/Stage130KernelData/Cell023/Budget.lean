import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage130KernelData.Cell023.Parameters

namespace ForestUnimodality.Stage130KernelData.Cell023
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(111681214004715886400135810653/1000000000000000000000000000000), (14189404684814147459374096801/62500000000000000000000000000)]
def R : ℚ := (1030670341379310344827586206897/1000000000000000000000000000000)
def D : ℚ := (358219917476923076923076923077/200000000000000000000000000000)
def vmax : ℚ := (638/2601)
def mlo : ℚ := (153/4)
def mhi : ℚ := (49261363636363636363636363636363/1000000000000000000000000000000)
def alpha : ℚ := (328783838900000000000000000000143/1300500000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (33217038209103539781297288050106675329994160348660133920303/80000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1963942442700225221585697/500000000000000000000000)) (.exp (-17087225742721530619220779029909/4000000000000000000000000000000) (6978274380195364178103/500000000000000000000000) (13956548760390728356207/1000000000000000000000000) { parts := 5, inner := (-17087225742721530619220779029909/20000000000000000000000000000000), terms := 40, innerLo := (425554911693716292540365019801/1000000000000000000000000000000), innerHi := (212777455846858146270182509901/500000000000000000000000000000) }))) (.mul (.rat (2019088136348623763183241/100000000000000000000000)) (.exp (-2170978916776564561284236810553/250000000000000000000000000000) (5290215530565513673/31250000000000000000000) (169286896978096437537/1000000000000000000000000) { parts := 9, inner := (-241219879641840506809359645617/250000000000000000000000000000), terms := 40, innerLo := (381029103906297199221938127491/1000000000000000000000000000000), innerHi := (95257275976574299805484531873/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (1427807500446861941773349496757160870476499904594069993329716686922411208332039554844515389/3825000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1963942442700225221585697/500000000000000000000000)) (.exp (-5501568894436856449370326581599417566500178817163199913575039/1000000000000000000000000000000000000000000000000000000000000) (2040182376255333138263/500000000000000000000000) (4080364752510666276527/1000000000000000000000000) { parts := 6, inner := (-5501568894436856449370326581599417566500178817163199913575039/6000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (399745114363412505536600308393/1000000000000000000000000000000), innerHi := (199872557181706252768300154197/500000000000000000000000000000) }))) (.mul (.rat (2019088136348623763183241/100000000000000000000000)) (.exp (-698989423962151468595303518549252334015200572815253125574763/62500000000000000000000000000000000000000000000000000000000) (13897094292373832573/1000000000000000000000000) (6948547146186916287/500000000000000000000000) { parts := 12, inner := (-698989423962151468595303518549252334015200572815253125574763/750000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (39377094420853248917964009491/100000000000000000000000000000), innerHi := (393770944208532489179640094911/1000000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck = true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mhi := by
  norm_num [budgetExpression_hi, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_hi_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mhi := by
  rw [← budgetExpression_hi_eval]
  exact budgetExpression_hi.positiveCheck_sound budgetExpression_hi_checked

theorem budget_positive {m : ℝ} (hm : m ∈ Set.Icc (mlo : ℝ) (mhi : ℝ)) :
    0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D m := by
  have hs := row.signCheck_sound row_checked
  have hdM : (0 : ℝ) ≤ row.dM := by norm_num [row]
  have hT : ∀ i ∈ row.terms, (0 : ℝ) ≤ row.price i := by
    intro i hi
    exact hs.price i hi
  exact KernelBudget.budget_pos_of_endpoints row.terms (∅ : Finset ℤ)
    row.A row.B row.dδ row.dM alpha varianceIntercept D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ)) (fun _ => 0) (fun _ => 0)
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage130KernelData.Cell023
