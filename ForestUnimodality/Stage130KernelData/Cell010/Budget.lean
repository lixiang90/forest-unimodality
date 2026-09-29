import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage130KernelData.Cell010.Parameters

namespace ForestUnimodality.Stage130KernelData.Cell010
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(29810624092422477535348571433/250000000000000000000000000000), (100372837919489952261725275127/500000000000000000000000000000)]
def R : ℚ := (3803687/2500000)
def D : ℚ := (3383039/2000000)
def vmax : ℚ := (2/9)
def mlo : ℚ := (99/2)
def mhi : ℚ := (255/4)
def alpha : ℚ := (3803687/11250000)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (2390759041129754593158172288137263/6250000000000000000000000000000000)) (.mul (.rat (2735236125664903372722847/2000000000000000000000000)) (.exp (-2951251785149825275999508571867/500000000000000000000000000000) (2732595004156587872513/1000000000000000000000000) (1366297502078293936257/500000000000000000000000) { parts := 6, inner := (-983750595049941758666502857289/1000000000000000000000000000000), terms := 40, innerLo := (373906095348461577367351788477/1000000000000000000000000000000), innerHi := (186953047674230788683675894239/500000000000000000000000000000) }))) (.mul (.rat (4606724665938496943162761/625000000000000000000000)) (.exp (-9936910954029505273910802237573/1000000000000000000000000000000) (48356449451525681163/1000000000000000000000000) (12089112362881420291/250000000000000000000000) { parts := 10, inner := (-9936910954029505273910802237573/10000000000000000000000000000000), terms := 40, innerLo := (370207694109364786012248079347/1000000000000000000000000000000), innerHi := (92551923527341196503062019837/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (2730318147093776631920437283734861/7500000000000000000000000000000000)) (.mul (.rat (2735236125664903372722847/2000000000000000000000000)) (.exp (-1520341828713546354302777143083/200000000000000000000000000000) (499596820628218354257/1000000000000000000000000) (249798410314109177129/500000000000000000000000) { parts := 8, inner := (-1520341828713546354302777143083/1600000000000000000000000000000), terms := 40, innerLo := (193329203894182842415878562767/500000000000000000000000000000), innerHi := (77331681557673136966351425107/200000000000000000000000000000) }))) (.mul (.rat (4606724665938496943162761/625000000000000000000000)) (.exp (-5119014733893987565347989031477/400000000000000000000000000000) (276758119307829007/100000000000000000000000) (2767581193078290071/1000000000000000000000000) { parts := 13, inner := (-5119014733893987565347989031477/5200000000000000000000000000000), terms := 40, innerLo := (373653676077060447788968510247/1000000000000000000000000000000), innerHi := (46706709509632555973621063781/125000000000000000000000000000) })))
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
end ForestUnimodality.Stage130KernelData.Cell010
