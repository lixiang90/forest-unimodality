import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage130KernelData.Cell238.Parameters

namespace ForestUnimodality.Stage130KernelData.Cell238
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(118379618915763648402513570053/1000000000000000000000000000000), (120673627134489075602089476257/1000000000000000000000000000000)]
def R : ℚ := (5095673/2500000)
def D : ℚ := (1405101735662650602409638554217/500000000000000000000000000000)
def vmax : ℚ := (3569/15876)
def mlo : ℚ := (63/2)
def mhi : ℚ := (8089766596933620079738246088499/200000000000000000000000000000)
def alpha : ℚ := (18186456937/39690000000)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (53642559595098212715268433489705364109092335412591924405349/196875000000000000000000000000000000000000000000000000000000)) (.mul (.rat (33554307631986803883705761/10000000000000000000000000)) (.exp (-7457915991693109849358354913339/2000000000000000000000000000000) (4803569900242368410867/200000000000000000000000) (375278898456435032099/15625000000000000000000) { parts := 4, inner := (-7457915991693109849358354913339/8000000000000000000000000000000), terms := 40, innerLo := (393671096422309906641038772383/1000000000000000000000000000000), innerHi := (12302221763197184582532461637/31250000000000000000000000000) }))) (.mul (.rat (42095870733726847845446173/10000000000000000000000000)) (.exp (-7602438509472811762931637004191/2000000000000000000000000000000) (22343512807861688761251/1000000000000000000000000) (5585878201965422190313/250000000000000000000000) { parts := 4, inner := (-7602438509472811762931637004191/8000000000000000000000000000000), terms := 40, innerLo := (193311578731422515876078036801/500000000000000000000000000000), innerHi := (386623157462845031752156073603/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (61974518352196490484735061486483359882999056264425848504731749042517982452141597123654143/275625000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (33554307631986803883705761/10000000000000000000000000)) (.exp (-957663486862476089929261483840913037464183047198395474120447/200000000000000000000000000000000000000000000000000000000000) (4163227705246312792059/500000000000000000000000) (8326455410492625584119/1000000000000000000000000) { parts := 5, inner := (-957663486862476089929261483840913037464183047198395474120447/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (191894283105146915287534703117/500000000000000000000000000000), innerHi := (76757713242058766115013881247/200000000000000000000000000000) }))) (.mul (.rat (42095870733726847845446173/10000000000000000000000000)) (.exp (-976221477923412244720307100432296810442217813501141781268243/200000000000000000000000000000000000000000000000000000000000) (7588605829557607476151/1000000000000000000000000) (948575728694700934519/125000000000000000000000) { parts := 5, inner := (-976221477923412244720307100432296810442217813501141781268243/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (37673190270292961119401892719/100000000000000000000000000000), innerHi := (376731902702929611194018927191/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage130KernelData.Cell238
