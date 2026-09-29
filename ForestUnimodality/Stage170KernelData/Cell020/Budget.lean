import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell020.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell020
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(104249861087605159830651630899/1000000000000000000000000000000), (6268543550698558674211104133/50000000000000000000000000000)]
def R : ℚ := (8458603/6250000)
def D : ℚ := (63356039/40000000)
def vmax : ℚ := (10/49)
def mlo : ℚ := (1958887/12800)
def mhi : ℚ := (1225/8)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (156979151374364802285604862605406840378727/358400000000000000000000000000000000000000)) (.mul (.rat (10643420875373686840248411/100000000000000000000000)) (.exp (-204213697636315608725185681296849413/12800000000000000000000000000000000) (11780971158394601/100000000000000000000000) (117809711583946011/1000000000000000000000000) { parts := 16, inner := (-204213697636315608725185681296849413/204800000000000000000000000000000000), terms := 40, innerLo := (368934117039933392578700086743/1000000000000000000000000000000), innerHi := (46116764629991674072337510843/125000000000000000000000000000) }))) (.mul (.rat (3180249119403769419989203/62500000000000000000000)) (.exp (-12279368470397247505649367141779971/640000000000000000000000000000000) (581183382309633/125000000000000000000000) (929893411695413/200000000000000000000000) { parts := 20, inner := (-12279368470397247505649367141779971/12800000000000000000000000000000000), terms := 40, innerLo := (383151172370270556595794064693/1000000000000000000000000000000), innerHi := (191575586185135278297897032347/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (1120921308439806422416804536756310869/2560000000000000000000000000000000000)) (.mul (.rat (10643420875373686840248411/100000000000000000000000)) (.exp (-5108243193292652831701929914051/320000000000000000000000000000) (58373304893877241/500000000000000000000000) (116746609787754483/1000000000000000000000000) { parts := 16, inner := (-5108243193292652831701929914051/5120000000000000000000000000000), terms := 40, innerLo := (14749006217392110319304499331/40000000000000000000000000000), innerHi := (92181288858700689495653120819/250000000000000000000000000000) }))) (.mul (.rat (3180249119403769419989203/62500000000000000000000)) (.exp (-307158633984229375036344102517/16000000000000000000000000000) (36792453441173/8000000000000000000000) (2299528340073313/500000000000000000000000) { parts := 20, inner := (-307158633984229375036344102517/320000000000000000000000000000), terms := 40, innerLo := (5983474769969139106356418559/15625000000000000000000000000), innerHi := (382942385278024902806810787777/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell020
