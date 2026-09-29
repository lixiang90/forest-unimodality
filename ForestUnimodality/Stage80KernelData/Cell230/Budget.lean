import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage80KernelData.Cell230.Parameters

namespace ForestUnimodality.Stage80KernelData.Cell230
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(137374183529187119638413591987/1000000000000000000000000000000)]
def R : ℚ := (895980376470588235294117647059/500000000000000000000000000000)
def D : ℚ := (278865343/100000000)
def vmax : ℚ := (2/9)
def mlo : ℚ := (3862857142857142857142857142857/200000000000000000000000000000)
def mhi : ℚ := (81714285714285714285714285714283/4000000000000000000000000000000)
def alpha : ℚ := (-50971525658647919748520710059/250000000000000000000000000000)
def varianceIntercept : ℚ := (935250647522444737108369684071/100000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (2077555070393011603854501627537983469220432140528306923427527413192084747762628690124531/4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (28876896095000490483073463/5000000000000000000000000)) (.exp (-530656846089888530717529075332620375116638687554337369486859/200000000000000000000000000000000000000000000000000000000000) (35209779403202835173183/500000000000000000000000) (70419558806405670346367/1000000000000000000000000) { parts := 3, inner := (-176885615363296176905843025110873458372212895851445789828953/200000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (82590056318877743717543454623/200000000000000000000000000000), innerHi := (103237570398597179646929318279/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (841318031569469171671819583834483176882610575000920769287615061917009541497264648964284971/1600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (28876896095000490483073463/5000000000000000000000000)) (.exp (-11225433282670718919024653516651627127216135063532410020250321/4000000000000000000000000000000000000000000000000000000000000) (60424639368053900219247/1000000000000000000000000) (3776539960503368763703/62500000000000000000000) { parts := 3, inner := (-3741811094223572973008217838883875709072045021177470006750107/4000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (98102038316982742841524286737/250000000000000000000000000000), innerHi := (392408153267930971366097146949/1000000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck = true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mhi := by
  norm_num [budgetExpression_hi, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]

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
end ForestUnimodality.Stage80KernelData.Cell230
