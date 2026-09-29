import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell455.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell455
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(148122995254678314820666013409/1000000000000000000000000000000), (731610983851752886533442021/4000000000000000000000000000)]
def R : ℚ := (45415711/50000000)
def D : ℚ := (348727340837209302325581395349/200000000000000000000000000000)
def vmax : ℚ := (340/1369)
def mlo : ℚ := (185/4)
def mhi : ℚ := (48970588235294117647058823529411/1000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (82836982929140872733709674692843136609775754247572004244829/296000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (16821395450425402628980009/1000000000000000000000000)) (.exp (-5480550824423097648364642496133/800000000000000000000000000000) (1058726476391780721299/1000000000000000000000000) (10587264763917807213/10000000000000000000000) { parts := 7, inner := (-782935832060442521194948928019/800000000000000000000000000000), terms := 40, innerLo := (375810673595823513519664469219/1000000000000000000000000000000), innerHi := (18790533679791175675983223461/50000000000000000000000000000) }))) (.mul (.rat (12984375185743333602772509/500000000000000000000000)) (.exp (-27069606402514856801737354777/3200000000000000000000000000) (42386107054874959569/200000000000000000000000) (105965267637187398923/500000000000000000000000) { parts := 9, inner := (-27069606402514856801737354777/28800000000000000000000000000), terms := 40, innerLo := (390660302186995488824486608063/1000000000000000000000000000000), innerHi := (6104067221671804512882603251/15625000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (4651011498866168455201918017802785136178518289332238016135998042795712738624198237308701609/17112500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (16821395450425402628980009/1000000000000000000000000)) (.exp (-7253670208795276299306144480175916141238922893053372431872099/1000000000000000000000000000000000000000000000000000000000000) (176893169471542572059/250000000000000000000000) (707572677886170288237/1000000000000000000000000) { parts := 8, inner := (-7253670208795276299306144480175916141238922893053372431872099/8000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (403851203876391777944800004357/1000000000000000000000000000000), innerHi := (201925601938195888972400002179/500000000000000000000000000000) }))) (.mul (.rat (12984375185743333602772509/500000000000000000000000)) (.exp (-35827420238622604590534734263675911121012348659557356779631/4000000000000000000000000000000000000000000000000000000000) (5154033816588561517/40000000000000000000000) (64425422707357018963/500000000000000000000000) { parts := 9, inner := (-35827420238622604590534734263675911121012348659557356779631/36000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (14785889833465825342601222003/40000000000000000000000000000), innerHi := (92411811459161408391257637519/250000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell455
