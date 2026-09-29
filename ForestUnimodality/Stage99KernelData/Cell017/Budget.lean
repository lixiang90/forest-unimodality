import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage99KernelData.Cell017.Parameters

namespace ForestUnimodality.Stage99KernelData.Cell017
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(6460752661446166348280518249/62500000000000000000000000000), (216001119363675736740995670733/1000000000000000000000000000000)]
def R : ℚ := (1386175903846153846153846153847/1000000000000000000000000000000)
def D : ℚ := (2296765958762886597938144329897/1000000000000000000000000000000)
def vmax : ℚ := (1716/7225)
def mlo : ℚ := (32196969696969696969696969696969/1000000000000000000000000000000)
def mhi : ℚ := (85/2)
def alpha : ℚ := (594669462750000000000000000000363/1806250000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (5790341329361091514035229288294958817777188542780486390721445990595267942993447839839178803/14450000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (17574062720074283827642603/10000000000000000000000000)) (.exp (-208016657660198537728728807259465194020872325399211804487281/62500000000000000000000000000000000000000000000000000000000) (17927602708455192376431/500000000000000000000000) (35855205416910384752863/1000000000000000000000000) { parts := 4, inner := (-208016657660198537728728807259465194020872325399211804487281/250000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (87029812807880846082278866683/200000000000000000000000000000), innerHi := (54393633004925528801424291677/125000000000000000000000000000) }))) (.mul (.rat (10742143759653007606402753/1000000000000000000000000)) (.exp (-6954581494663802129918421216782046423462261680547119912108277/1000000000000000000000000000000000000000000000000000000000000) (190850643485283916739/200000000000000000000000) (59640826089151223981/62500000000000000000000) { parts := 7, inner := (-993511642094828875702631602397435203351751668649588558872611/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (370274135066111238931260883651/1000000000000000000000000000000), innerHi := (92568533766527809732815220913/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (238191142599920801075893938088673756195840179847061650314379/680000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (17574062720074283827642603/10000000000000000000000000)) (.exp (-109832795244584827920768810233/25000000000000000000000000000) (3089932073799433419199/250000000000000000000000) (12359728295197733676797/1000000000000000000000000) { parts := 5, inner := (-109832795244584827920768810233/125000000000000000000000000000), terms := 40, innerLo := (207669056164968405183210020363/500000000000000000000000000000), innerHi := (415338112329936810366420040727/1000000000000000000000000000000) }))) (.mul (.rat (10742143759653007606402753/1000000000000000000000000)) (.exp (-3672019029182487524596926402461/400000000000000000000000000000) (103075629420657315009/1000000000000000000000000) (10307562942065731501/100000000000000000000000) { parts := 10, inner := (-3672019029182487524596926402461/4000000000000000000000000000000), terms := 40, innerLo := (399314977072479070731642095771/1000000000000000000000000000000), innerHi := (99828744268119767682910523943/250000000000000000000000000000) })))
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
end ForestUnimodality.Stage99KernelData.Cell017
