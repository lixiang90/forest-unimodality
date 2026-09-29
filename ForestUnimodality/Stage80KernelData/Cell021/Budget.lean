import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage80KernelData.Cell021.Parameters

namespace ForestUnimodality.Stage80KernelData.Cell021
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(214173027808615080838750353641/1000000000000000000000000000000), (27234672974163416317005901711/125000000000000000000000000000)]
def R : ℚ := (9850373/10000000)
def D : ℚ := (90810693/50000000)
def vmax : ℚ := (5696/23409)
def mlo : ℚ := (765/32)
def mhi : ℚ := (3825/128)
def alpha : ℚ := (876683197/3657656250)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (1889082807939094858435235860070472437/4800000000000000000000000000000000000)) (.mul (.rat (35643611494934397398992587/5000000000000000000000000)) (.exp (-32768473254718107368328804107073/6400000000000000000000000000000) (1493895252014503466761/250000000000000000000000) (1195116201611602773409/200000000000000000000000) { parts := 6, inner := (-10922824418239369122776268035691/12800000000000000000000000000000), terms := 40, innerLo := (425987337354308845249857179787/1000000000000000000000000000000), innerHi := (106496834338577211312464294947/250000000000000000000000000000) }))) (.mul (.rat (76928091353376188976653793/10000000000000000000000000)) (.exp (-4166904965047002696501902961783/800000000000000000000000000000) (1367288677737197015321/250000000000000000000000) (1093830942189757612257/200000000000000000000000) { parts := 6, inner := (-1388968321682334232167300987261/1600000000000000000000000000000), terms := 40, innerLo := (83949226150202386529534621469/200000000000000000000000000000), innerHi := (209873065375505966323836553673/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (637771665362023934725508653980744031/1920000000000000000000000000000000000)) (.mul (.rat (35643611494934397398992587/5000000000000000000000000)) (.exp (-32768473254718107368328804107073/5120000000000000000000000000000) (207675462284477340063/125000000000000000000000) (332280739655163744101/200000000000000000000000) { parts := 7, inner := (-32768473254718107368328804107073/35840000000000000000000000000000), terms := 40, innerLo := (400797519165511005387564181299/1000000000000000000000000000000), innerHi := (4007975191655110053875641813/10000000000000000000000000000) }))) (.mul (.rat (76928091353376188976653793/10000000000000000000000000)) (.exp (-4166904965047002696501902961783/640000000000000000000000000000) (1487305764012246157931/1000000000000000000000000) (371826441003061539483/250000000000000000000000) { parts := 7, inner := (-4166904965047002696501902961783/4480000000000000000000000000000), terms := 40, innerLo := (394509240593732776386478178167/1000000000000000000000000000000), innerHi := (49313655074216597048309772271/125000000000000000000000000000) })))
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
end ForestUnimodality.Stage80KernelData.Cell021
