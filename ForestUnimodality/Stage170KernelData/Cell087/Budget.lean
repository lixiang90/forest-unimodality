import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell087.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell087
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(76042097093269813712208578429/1000000000000000000000000000000), (34107539458400355632431972723/200000000000000000000000000000)]
def R : ℚ := (9850373/10000000)
def D : ℚ := (90810693/50000000)
def vmax : ℚ := (5696/23409)
def mlo : ℚ := (1861551/20480)
def mhi : ℚ := (1575/16)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (32130903348325291599776566064024658486370273/62668800000000000000000000000000000000000000)) (.mul (.rat (69927370581836560958777227/10000000000000000000000000)) (.exp (-141556241886073514985775591383083379/20480000000000000000000000000000000) (39833523619580345889/40000000000000000000000) (497919045244754323613/500000000000000000000000) { parts := 7, inner := (-20222320269439073569396513054726197/20480000000000000000000000000000000), terms := 40, innerLo := (23283584277825679431017369211/62500000000000000000000000000), innerHi := (372537348445210870896277907377/1000000000000000000000000000000) }))) (.mul (.rat (4544308141645917231699059/200000000000000000000000)) (.exp (-63492924186324640427909371254473373/4096000000000000000000000000000000) (11582263516385143/62500000000000000000000) (185316216262162289/1000000000000000000000000) { parts := 16, inner := (-63492924186324640427909371254473373/65536000000000000000000000000000000), terms := 40, innerLo := (189764335210157446409142582763/500000000000000000000000000000), innerHi := (379528670420314892818285165527/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (519003590886998976605405199419395027519/1040400000000000000000000000000000000000)) (.mul (.rat (69927370581836560958777227/10000000000000000000000000)) (.exp (-4790652116875998263869140441027/640000000000000000000000000000) (70152755343883677243/125000000000000000000000) (112244408550213883589/200000000000000000000000) { parts := 8, inner := (-4790652116875998263869140441027/5120000000000000000000000000000), terms := 40, innerLo := (49040157129168694393362755179/125000000000000000000000000000), innerHi := (392321257033349555146902041433/1000000000000000000000000000000) }))) (.mul (.rat (4544308141645917231699059/200000000000000000000000)) (.exp (-2148774985879222404843214281549/128000000000000000000000000000) (6401419214738763/125000000000000000000000) (10242270743582021/200000000000000000000000) { parts := 17, inner := (-2148774985879222404843214281549/2176000000000000000000000000000), terms := 40, innerLo := (46563884632069355374156676383/125000000000000000000000000000), innerHi := (74502215411310968598650682213/200000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell087
