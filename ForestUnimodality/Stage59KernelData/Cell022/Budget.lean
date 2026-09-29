import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell022.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell022
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(139560268160001615847495416309/1000000000000000000000000000000)]
def alpha : ℚ := (72043009756250000000000000000039/292612500000000000000000000000000)
def D : ℚ := (5771073659/3200000000)
def mlo : ℚ := (8826923076923076923076923076923/500000000000000000000000000000)
def mhi : ℚ := (7355769230769230769230769230769/250000000000000000000000000000)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha 0 D m

def budgetExpression_lo : Expr := (.sub (.rat (1661342370778836795874050579150800369791479561635787466006878106832094296592310019703916267/1950750000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (248416113039460340061737/100000000000000000000000)) (.exp (-1231887751643091186038469155496739264594756922952627115737207/500000000000000000000000000000000000000000000000000000000000) (85112999176647498593423/1000000000000000000000000) (5319562448540468662089/62500000000000000000000) { parts := 3, inner := (-410629250547697062012823051832246421531585640984209038579069/500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (219938859711711333558348270641/500000000000000000000000000000), innerHi := (439877719423422667116696541283/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (110724478862609398644062529084314199021347665556334029146575682701234345840995073684608801/162562500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (248416113039460340061737/100000000000000000000000)) (.exp (-1026573126369242655032057629580592793784270768857881347211621/250000000000000000000000000000000000000000000000000000000000) (658748766665380364941/40000000000000000000000) (8234359583317254561763/500000000000000000000000) { parts := 5, inner := (-1026573126369242655032057629580592793784270768857881347211621/1250000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (219938859711711333558348270641/500000000000000000000000000000), innerHi := (439877719423422667116696541283/1000000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck=true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval = budget mhi := by
  norm_num [budgetExpression_hi, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
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
    row.A row.B row.dδ row.dM alpha 0 D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ))
    (fun j => (row.fixedPrice j : ℝ)) (fun j => (countBound j : ℝ))
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage59KernelData.Cell022
