import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell094.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell094
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(111681214004715886400135810653/1000000000000000000000000000000)]
def R : ℚ := (1030670341379310344827586206897/1000000000000000000000000000000)
def D : ℚ := (358219917476923076923076923077/200000000000000000000000000000)
def vmax : ℚ := (638/2601)
def mlo : ℚ := (6131590909090909090909090909090861/80000000000000000000000000000000)
def mhi : ℚ := (141026590909090909090909090909089803/1600000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (371519579770770553285973922567842366487659840146970553249853716400862260602006205528680837529351/832320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (8551930408525008076026097/250000000000000000000000)) (.exp (-684783516507552249815741826274378038239799227754190393468742233/80000000000000000000000000000000000000000000000000000000000000) (191658779647982659047/1000000000000000000000000) (23957347455997832381/125000000000000000000000) { parts := 9, inner := (-684783516507552249815741826274378038239799227754190393468742233/720000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (4829004925801025730737197019/12500000000000000000000000000), innerHi := (386320394064082058458975761521/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (145263190878211570778529036333019717224197197077172842376705954404581057930264492607269228220473479/332928000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (8551930408525008076026097/250000000000000000000000)) (.exp (-15750020879673701745762062004310694879515382238346379049781071359/1600000000000000000000000000000000000000000000000000000000000000) (53077202688930741691/1000000000000000000000000) (13269300672232685423/250000000000000000000000) { parts := 10, inner := (-15750020879673701745762062004310694879515382238346379049781071359/16000000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (23354513235694312311273955831/62500000000000000000000000000), innerHi := (373672211771108996980383293297/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell094
