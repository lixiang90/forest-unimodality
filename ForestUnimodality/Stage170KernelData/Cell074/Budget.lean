import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell074.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell074
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(36569303033796021002868742701/500000000000000000000000000000), (10804182922909485933519621241/62500000000000000000000000000)]
def R : ℚ := (1417165201298701298701298701299/1000000000000000000000000000000)
def D : ℚ := (2283914681359044995408631772269/1000000000000000000000000000000)
def vmax : ℚ := (15554/65025)
def mlo : ℚ := (767966584158415841584158415841573437/8000000000000000000000000000000000)
def mhi : ℚ := (425/4)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (22533552181625041819410953453600036189791389549054587437358705529865541918238958250429759212871109217/55488000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (33780132037790435717283799/5000000000000000000000000)) (.exp (-28084002735918323718610276750737747776780286282567413569749233337/4000000000000000000000000000000000000000000000000000000000000000) (22323287584318315757/25000000000000000000000) (892931503372732630281/1000000000000000000000000) { parts := 8, inner := (-28084002735918323718610276750737747776780286282567413569749233337/32000000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (415769156293708146740161872791/1000000000000000000000000000000), innerHi := (51971144536713518342520234099/125000000000000000000000000000) }))) (.mul (.rat (319025542732726741235183/20000000000000000000000)) (.exp (-8297251453929486983923013383170177480693738113518154169726575317/500000000000000000000000000000000000000000000000000000000000000) (1552526299802537/25000000000000000000000) (62101051992101481/1000000000000000000000000) { parts := 17, inner := (-8297251453929486983923013383170177480693738113518154169726575317/8500000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (94189968837569870853206947641/250000000000000000000000000000), innerHi := (75351975070055896682565558113/200000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (3202730407016844051239589402904669766527988259739621846941317/8160000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (33780132037790435717283799/5000000000000000000000000)) (.exp (-621678151574532357048768625917/80000000000000000000000000000) (105450252578143836777/250000000000000000000000) (421801010312575347109/1000000000000000000000000) { parts := 8, inner := (-621678151574532357048768625917/640000000000000000000000000000), terms := 40, innerLo := (7571265009304520175450579213/20000000000000000000000000000), innerHi := (378563250465226008772528960651/1000000000000000000000000000000) }))) (.mul (.rat (319025542732726741235183/20000000000000000000000)) (.exp (-183671109689461260869833561097/10000000000000000000000000000) (105503060396639/10000000000000000000000) (10550306039663901/1000000000000000000000000) { parts := 19, inner := (-183671109689461260869833561097/190000000000000000000000000000), terms := 40, innerLo := (95084965623055423193871188173/250000000000000000000000000000), innerHi := (380339862492221692775484752693/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell074
