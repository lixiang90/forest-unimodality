import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage130KernelData.Cell236.Parameters

namespace ForestUnimodality.Stage130KernelData.Cell236
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(115176453448796176308624641393/1000000000000000000000000000000), (117202945087834829656618761841/1000000000000000000000000000000)]
def R : ℚ := (950083027272727272727272727273/500000000000000000000000000000)
def D : ℚ := (1427449926666666666666666666667/500000000000000000000000000000)
def vmax : ℚ := (45/196)
def mlo : ℚ := (63/2)
def mhi : ℚ := (40933124174714097886579939645583/1000000000000000000000000000000)
def alpha : ℚ := (8550747245454545454545454545457/19600000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (6098227833577547220039059902466686564103827518751614229313/20000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (10376330421180185226148751/2000000000000000000000000)) (.exp (-7256116567274159107443352407759/2000000000000000000000000000000) (6641930334224758624681/250000000000000000000000) (1062708853475961379949/40000000000000000000000) { parts := 4, inner := (-7256116567274159107443352407759/8000000000000000000000000000000), terms := 40, innerLo := (100931931788630765756239606247/250000000000000000000000000000), innerHi := (403727727154523063024958424989/1000000000000000000000000000000) }))) (.mul (.rat (38269654593856885504976617/10000000000000000000000000)) (.exp (-7383785540533594268366981995983/2000000000000000000000000000000) (24924780483187547672621/1000000000000000000000000) (12462390241593773836311/500000000000000000000000) { parts := 4, inner := (-7383785540533594268366981995983/8000000000000000000000000000000), terms := 40, innerLo := (198667963459271850136023751001/500000000000000000000000000000), innerHi := (397335926918543700272047502003/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (8426292142265015534443687172867373938970465881735199623428215427991004798396538606645339/35000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (10376330421180185226148751/2000000000000000000000000)) (.exp (-4714532071022751697648887543635363226894678750953636891417119/1000000000000000000000000000000000000000000000000000000000000) (4482029814455961947857/500000000000000000000000) (1792811925782384779143/200000000000000000000000) { parts := 5, inner := (-4714532071022751697648887543635363226894678750953636891417119/5000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (77898831467226784004307364007/200000000000000000000000000000), innerHi := (97373539334033480005384205009/250000000000000000000000000000) }))) (.mul (.rat (38269654593856885504976617/10000000000000000000000000)) (.exp (-4797482704922540794524681130026270149988498230458217824598303/1000000000000000000000000000000000000000000000000000000000000) (8250489847674198497433/1000000000000000000000000) (4125244923837099248717/500000000000000000000000) { parts := 5, inner := (-4797482704922540794524681130026270149988498230458217824598303/5000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (383085705384786119857769433937/1000000000000000000000000000000), innerHi := (191542852692393059928884716969/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage130KernelData.Cell236
