import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell461.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell461
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(7653122560822125407875437163/62500000000000000000000000000), (18624791398933283800976461871/100000000000000000000000000000)]
def R : ℚ := (5091347/6250000)
def D : ℚ := (165910603286307053941908713693/100000000000000000000000000000)
def vmax : ℚ := (90/361)
def mlo : ℚ := (44861111111111111111111111111111/1000000000000000000000000000000)
def mhi : ℚ := (95/2)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (1445178812223003880787080052265332571670574480142288587290777676392682213258595991168565667/18050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (519565634793451636141981/62500000000000000000000)) (.exp (-343327581547992570381078639395693594097493241986065791618093/62500000000000000000000000000000000000000000000000000000000) (4114486233525778348579/1000000000000000000000000) (205724311676288917429/50000000000000000000000) { parts := 6, inner := (-343327581547992570381078639395693594097493241986065791618093/375000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (25018769902981349631587809777/62500000000000000000000000000), innerHi := (400300318447701594105404956433/1000000000000000000000000000000) }))) (.mul (.rat (43951856072226192395646649/500000000000000000000000)) (.exp (-835528836368812592738249608935136819467622340746244335948681/100000000000000000000000000000000000000000000000000000000000) (47029933494222862079/200000000000000000000000) (58787416867778577599/250000000000000000000000) { parts := 9, inner := (-835528836368812592738249608935136819467622340746244335948681/900000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (79039837127601059028678547023/200000000000000000000000000000), innerHi := (98799796409501323785848183779/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (2378603311559398615238267626507715137099503442864692680681/38000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (519565634793451636141981/62500000000000000000000)) (.exp (-145409328655620382749633306097/25000000000000000000000000000) (2978387756361712099823/1000000000000000000000000) (186149234772607006239/62500000000000000000000) { parts := 6, inner := (-145409328655620382749633306097/150000000000000000000000000000), terms := 40, innerLo := (75862450766411181756222374123/200000000000000000000000000000), innerHi := (47414031729006988597638983827/125000000000000000000000000000) }))) (.mul (.rat (43951856072226192395646649/500000000000000000000000)) (.exp (-353871036579732392218552775549/40000000000000000000000000000) (143844757262690014393/1000000000000000000000000) (71922378631345007197/500000000000000000000000) { parts := 9, inner := (-353871036579732392218552775549/360000000000000000000000000000), terms := 40, innerLo := (93549042383299338950379433621/250000000000000000000000000000), innerHi := (74839233906639471160303546897/200000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck = true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mhi := by
  norm_num [budgetExpression_hi, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

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
end ForestUnimodality.Stage170KernelData.Cell461
