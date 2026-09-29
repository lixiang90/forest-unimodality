import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage130KernelData.Cell239.Parameters

namespace ForestUnimodality.Stage130KernelData.Cell239
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(119984313105215384271646889291/1000000000000000000000000000000), (61304787699704703640566705149/500000000000000000000000000000)]
def R : ℚ := (524460776470588235294117647059/250000000000000000000000000000)
def D : ℚ := (278865343/100000000)
def vmax : ℚ := (2/9)
def mlo : ℚ := (156/5)
def mhi : ℚ := (5038028803202905671217850302067/125000000000000000000000000000)
def alpha : ℚ := (174820258823529411764705882353/375000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (43936499617805779002290230220291922203739935620742434039/156250000000000000000000000000000000000000000000000000000)) (.mul (.rat (10708698236061389152951051/2000000000000000000000000)) (.exp (-4679388211103399986594228682349/1250000000000000000000000000000) (23670858918778840306539/1000000000000000000000000) (1183542945938942015327/50000000000000000000000) { parts := 4, inner := (-4679388211103399986594228682349/5000000000000000000000000000000), terms := 40, innerLo := (392241466752246696843717156907/1000000000000000000000000000000), innerHi := (98060366688061674210929289227/250000000000000000000000000000) }))) (.mul (.rat (2200368083949227893114653/1250000000000000000000000)) (.exp (-2390886720288483441982101500811/625000000000000000000000000000) (10904650460080169519249/500000000000000000000000) (21809300920160339038499/1000000000000000000000000) { parts := 4, inner := (-2390886720288483441982101500811/2500000000000000000000000000000), terms := 40, innerLo := (192145598527227722518804087121/500000000000000000000000000000), innerHi := (384291197054455445037608174243/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (42244399560665428815492823276109889501504557400185979155639138116005498634200418226849/187500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (10708698236061389152951051/2000000000000000000000000)) (.exp (-604484425356590973065496644491844285236326824876605257464497/125000000000000000000000000000000000000000000000000000000000) (793973481533919049271/100000000000000000000000) (7939734815339190492711/1000000000000000000000000) { parts := 5, inner := (-604484425356590973065496644491844285236326824876605257464497/625000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (190077715570961274407301425859/500000000000000000000000000000), innerHi := (380155431141922548814602851719/1000000000000000000000000000000) }))) (.mul (.rat (2200368083949227893114653/1250000000000000000000000)) (.exp (-308855286205351500632830415696049712550315171290772574242983/62500000000000000000000000000000000000000000000000000000000) (7142556030087574864319/1000000000000000000000000) (22320487594023671451/3125000000000000000000) { parts := 5, inner := (-308855286205351500632830415696049712550315171290772574242983/312500000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (93048792118053821709177355293/250000000000000000000000000000), innerHi := (372195168472215286836709421173/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage130KernelData.Cell239
