import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell300.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell300
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(21780843788482408525269670883/200000000000000000000000000000)]
def R : ℚ := (1258218833/800000000)
def D : ℚ := (470607184888888888888888888889/200000000000000000000000000000)
def vmax : ℚ := (2520/10609)
def mlo : ℚ := (284785662161658141006405349193909/5000000000000000000000000000000)
def mhi : ℚ := (6550070229718137243147323031459907/100000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (4799828243440146013965134832540297195140377540236470985904703832277270036683658302016152320407/13261250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (16185513754751941206677657/1000000000000000000000000)) (.exp (-6202872020742601403620344234538139709773371418847269778251647/1000000000000000000000000000000000000000000000000000000000000) (126475651955502549161/62500000000000000000000) (2023610431288040786577/1000000000000000000000000) { parts := 7, inner := (-886124574391800200517192033505448529967624488406752825464521/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (412250306363960464430852419449/1000000000000000000000000000000), innerHi := (8245006127279209288617048389/20000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (3629424019909718241857190595501851529222551779350856899234366651042580181848431610332084160661581/10609000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (16185513754751941206677657/1000000000000000000000000)) (.exp (-142666056477079832283267917394377213324787542633487204899787881/20000000000000000000000000000000000000000000000000000000000000) (79807911497659052241/100000000000000000000000) (798079114976590522411/1000000000000000000000000) { parts := 8, inner := (-142666056477079832283267917394377213324787542633487204899787881/160000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (204986730021429121882583255593/500000000000000000000000000000), innerHi := (409973460042858243765166511187/1000000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck = true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mhi := by
  norm_num [budgetExpression_hi, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

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
end ForestUnimodality.Stage170KernelData.Cell300
