import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell062.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell062
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(49669039857309676523113134711/500000000000000000000000000000), (82387857711637582465561905109/500000000000000000000000000000)]
def R : ℚ := (212243441/160000000)
def D : ℚ := (2322293575442247658688865764829/1000000000000000000000000000000)
def vmax : ℚ := (608/2601)
def mlo : ℚ := (408234868421052631578947368421048149/4000000000000000000000000000000000)
def mhi : ℚ := (425/4)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (18625651611917402022200807487407515128815688741263004542707097797518796243936309607311047357746629427/41616000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (7984934831593136550509371/500000000000000000000000)) (.exp (-20276633950748834570455653297016610907239178568008431735654199939/2000000000000000000000000000000000000000000000000000000000000000) (39535285723124987707/1000000000000000000000000) (9883821430781246927/250000000000000000000000) { parts := 11, inner := (-20276633950748834570455653297016610907239178568008431735654199939/22000000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (397855987520099943307687941181/1000000000000000000000000000000), innerHi := (198927993760049971653843970591/500000000000000000000000000000) }))) (.mul (.rat (16892766647154418002685361/10000000000000000000000000)) (.exp (-33633596252402774841304655705605783979397187238880999503058093241/2000000000000000000000000000000000000000000000000000000000000000) (776921958931321/15625000000000000000000) (9944601074320909/200000000000000000000000) { parts := 17, inner := (-33633596252402774841304655705605783979397187238880999503058093241/34000000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (92966340606047598469026739789/250000000000000000000000000000), innerHi := (371865362424190393876106959157/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (10771918481537321521559983148609670661626443661798398626716383/24480000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (7984934831593136550509371/500000000000000000000000)) (.exp (-844373677574264500892923290087/80000000000000000000000000000) (26071417212598064281/1000000000000000000000000) (13035708606299032141/500000000000000000000000) { parts := 11, inner := (-844373677574264500892923290087/880000000000000000000000000000), terms := 40, innerLo := (383078426169117916871666391077/1000000000000000000000000000000), innerHi := (191539213084558958435833195539/500000000000000000000000000000) }))) (.mul (.rat (16892766647154418002685361/10000000000000000000000000)) (.exp (-1400593581097838901914552386853/80000000000000000000000000000) (24924370835525821/1000000000000000000000000) (12462185417762911/500000000000000000000000) { parts := 18, inner := (-1400593581097838901914552386853/1440000000000000000000000000000), terms := 40, innerLo := (189042842091370872035888431131/500000000000000000000000000000), innerHi := (378085684182741744071776862263/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell062
