import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell167.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell167
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(50282439637337384451434036731/500000000000000000000000000000)]
def alpha : ℚ := (174292914713723249302977721267/1000000000000000000000000000000)
def D : ℚ := (374722705507204641461891099277/250000000000000000000000000000)
def mlo : ℚ := (17044729990050593789030250428671/1000000000000000000000000000000)
def mhi : ℚ := (6865238468214822498359406422659/250000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (3601835193002128802212068815942133560649923481054094452826193005040037462993778102041/2000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (2417972324097188430158667/250000000000000000000000)) (.exp (-857050606859433219650455173880038134748496273550792709514501/500000000000000000000000000000000000000000000000000000000000) (180125542347029637304393/1000000000000000000000000) (90062771173514818652197/500000000000000000000000) { parts := 2, inner := (-857050606859433219650455173880038134748496273550792709514501/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (53051499499753426695140679059/125000000000000000000000000000), innerHi := (424411995998027413561125432473/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (334965509747643854392622340064682627680808025052347885154302828045846184457290414389/500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (2417972324097188430158667/250000000000000000000000)) (.exp (-345200938873938380136988889479452122234310850302000316687729/125000000000000000000000000000000000000000000000000000000000) (63190107878392851335509/1000000000000000000000000) (6319010787839285133551/100000000000000000000000) { parts := 3, inner := (-345200938873938380136988889479452122234310850302000316687729/375000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (79661111407931505173523479953/200000000000000000000000000000), innerHi := (199152778519828762933808699883/500000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck=true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval = budget mhi := by
  norm_num [budgetExpression_hi, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_hi_positive : 0 < budget mhi := by
  rw [← budgetExpression_hi_eval]
  exact budgetExpression_hi.positiveCheck_sound budgetExpression_hi_checked

theorem budget_positive {m : ℝ} (hm : m ∈ Set.Icc (mlo : ℝ) (mhi : ℝ)) :
    0 < budget m := by
  have hs := row.signCheck_sound row_checked
  have hdM : (0 : ℝ) ≤ row.dM := by norm_num [row]
  have hT : ∀ i ∈ row.terms, (0 : ℝ) ≤ row.price i := by
    intro i hi
    exact hs.price i hi
  exact KernelBudget.budget_pos_of_endpoints row.terms row.fixedIndices
    row.A row.B row.dδ row.dM alpha varianceIntercept D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ))
    (fun j => (row.fixedPrice j : ℝ)) (fun j => (countBound j : ℝ))
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage59KernelData.Cell167
