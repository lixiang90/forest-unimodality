import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage80KernelData.Cell231.Parameters

namespace ForestUnimodality.Stage80KernelData.Cell231
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(137374183529187119638413591987/1000000000000000000000000000000)]
def R : ℚ := (895980376470588235294117647059/500000000000000000000000000000)
def D : ℚ := (278865343/100000000)
def vmax : ℚ := (2/9)
def mlo : ℚ := (81714285714285714285714285714283/4000000000000000000000000000000)
def mhi : ℚ := (43085714285714285714285714285713/2000000000000000000000000000000)
def alpha : ℚ := (895980376470588235294117647059/2250000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.rat (5392725011935679084906447737198144380365373276265888289121824497224968925716845577674414813/14400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (291641523747185482662303/50000000000000000000000)) (.exp (-11225433282670718919024653516651627127216135063532410020250321/4000000000000000000000000000000000000000000000000000000000000) (60424639368053900219247/1000000000000000000000000) (3776539960503368763703/62500000000000000000000) { parts := 3, inner := (-3741811094223572973008217838883875709072045021177470006750107/4000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (98102038316982742841524286737/250000000000000000000000000000), innerHi := (392408153267930971366097146949/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (1278258760661437624228559568891313664196457580544624829895653709190269129148651415308970373/3600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (291641523747185482662303/50000000000000000000000)) (.exp (-5918864821771833611849362763325423376049748187989036325381731/2000000000000000000000000000000000000000000000000000000000000) (6481042171814994893179/125000000000000000000000) (51848337374519959145433/1000000000000000000000000) { parts := 3, inner := (-1972954940590611203949787587775141125349916062663012108460577/2000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (372887888964791986141444066151/1000000000000000000000000000000), innerHi := (46610986120598998267680508269/125000000000000000000000000000) })))
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
end ForestUnimodality.Stage80KernelData.Cell231
