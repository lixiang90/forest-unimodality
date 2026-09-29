import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage99KernelData.Cell010.Parameters

namespace ForestUnimodality.Stage99KernelData.Cell010
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(29810624092422477535348571433/250000000000000000000000000000), (12549398151803045997099287937/62500000000000000000000000000)]
def R : ℚ := (3803687/2500000)
def D : ℚ := (3383039/2000000)
def vmax : ℚ := (2/9)
def mlo : ℚ := (75/2)
def mhi : ℚ := (99/2)
def alpha : ℚ := (3803687/11250000)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (4524347414410209088963416357384749/12000000000000000000000000000000000)) (.mul (.rat (44794915838539950403429657/50000000000000000000000000)) (.exp (-89431872277267432606045714299/20000000000000000000000000000) (2857271944345160296461/250000000000000000000000) (2285817555476128237169/200000000000000000000000) { parts := 5, inner := (-89431872277267432606045714299/100000000000000000000000000000), terms := 40, innerLo := (408886068539544214873351303283/1000000000000000000000000000000), innerHi := (102221517134886053718337825821/250000000000000000000000000000) }))) (.mul (.rat (68247138212465756623714697/10000000000000000000000000)) (.exp (-37648194455409137991297863811/5000000000000000000000000000) (67116514082015217153/125000000000000000000000) (21477284506244869489/40000000000000000000000) { parts := 8, inner := (-37648194455409137991297863811/40000000000000000000000000000), terms := 40, innerLo := (195078733192655544490764995097/500000000000000000000000000000), innerHi := (78031493277062217796305998039/200000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (36285036701116187732131702515232239/100000000000000000000000000000000000)) (.mul (.rat (44794915838539950403429657/50000000000000000000000000)) (.exp (-2951251785149825275999508571867/500000000000000000000000000000) (2732595004156587872513/1000000000000000000000000) (1366297502078293936257/500000000000000000000000) { parts := 6, inner := (-983750595049941758666502857289/1000000000000000000000000000000), terms := 40, innerLo := (373906095348461577367351788477/1000000000000000000000000000000), innerHi := (186953047674230788683675894239/500000000000000000000000000000) }))) (.mul (.rat (68247138212465756623714697/10000000000000000000000000)) (.exp (-1242390417028501553712829505763/125000000000000000000000000000) (964991695198708219/20000000000000000000000) (48249584759935410951/1000000000000000000000000) { parts := 10, inner := (-1242390417028501553712829505763/1250000000000000000000000000000), terms := 40, innerLo := (370125799077634547783804581303/1000000000000000000000000000000), innerHi := (46265724884704318472975572663/125000000000000000000000000000) })))
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
end ForestUnimodality.Stage99KernelData.Cell010
