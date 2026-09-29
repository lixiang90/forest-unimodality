import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage130KernelData.Cell004.Parameters

namespace ForestUnimodality.Stage130KernelData.Cell004
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(104249861087605159830651630899/1000000000000000000000000000000), (44957735004316453062289087759/250000000000000000000000000000)]
def R : ℚ := (8458603/6250000)
def D : ℚ := (63356039/40000000)
def vmax : ℚ := (10/49)
def mlo : ℚ := (231/4)
def mhi : ℚ := (595/8)
def alpha : ℚ := (8458603/30625000)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (62434135890115989286603275321243383097/140000000000000000000000000000000000000)) (.mul (.rat (10840060370943092049600409/10000000000000000000000000)) (.exp (-24081717911236791920880526737669/4000000000000000000000000000000) (60715658247387433559/25000000000000000000000) (2428626329895497342361/1000000000000000000000000) { parts := 7, inner := (-3440245415890970274411503819667/4000000000000000000000000000000), terms := 40, innerLo := (423136120439324939650279335391/1000000000000000000000000000000), innerHi := (13223003763728904364071229231/31250000000000000000000000000) }))) (.mul (.rat (25105730226837734697653559/5000000000000000000000000)) (.exp (-10385236785997100657388779272329/1000000000000000000000000000000) (15442548533063475159/500000000000000000000000) (30885097066126950319/1000000000000000000000000) { parts := 11, inner := (-944112435090645514308070842939/1000000000000000000000000000000), terms := 40, innerLo := (389024702390510570821572543941/1000000000000000000000000000000), innerHi := (194512351195255285410786271971/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (23635752758742024528101391945762197353/56000000000000000000000000000000000000)) (.mul (.rat (10840060370943092049600409/10000000000000000000000000)) (.exp (-12405733469425014019847544076981/1600000000000000000000000000000) (429201772091956323911/1000000000000000000000000) (53650221511494540489/125000000000000000000000) { parts := 8, inner := (-12405733469425014019847544076981/12800000000000000000000000000000), terms := 40, innerLo := (189693606114156322370433896823/500000000000000000000000000000), innerHi := (379387212228312644740867793647/1000000000000000000000000000000) }))) (.mul (.rat (25105730226837734697653559/5000000000000000000000000)) (.exp (-5349970465513657914412401443321/400000000000000000000000000000) (1553614876762546931/1000000000000000000000000) (388403719190636733/250000000000000000000000) { parts := 14, inner := (-764281495073379702058914491903/800000000000000000000000000000), terms := 40, innerLo := (38467676496871866932765422723/100000000000000000000000000000), innerHi := (384676764968718669327654227231/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage130KernelData.Cell004
