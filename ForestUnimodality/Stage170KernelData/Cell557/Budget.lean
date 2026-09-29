import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell557.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell557
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(6194046934040984496806347819/50000000000000000000000000000)]
def R : ℚ := (22914583/10000000)
def D : ℚ := (342313033551401869158878504673/125000000000000000000000000000)
def vmax : ℚ := (5243/24336)
def mlo : ℚ := (39745814003913943733092751650657/1000000000000000000000000000000)
def mhi : ℚ := (263023769143548157057231444747/6250000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (24916727926410697245997096836656599752635925574327462792812660799758075644303359540210979/100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (15841132036981941944020491/2500000000000000000000000)) (.exp (-246187437371906389366920778147084260876161403632087921867083/50000000000000000000000000000000000000000000000000000000000) (7271819472432580661479/1000000000000000000000000) (181795486810814516537/25000000000000000000000) { parts := 5, inner := (-246187437371906389366920778147084260876161403632087921867083/250000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (186766345994446682708633217607/500000000000000000000000000000), innerHi := (74706538397778673083453287043/200000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (18986705825451367735920196837969883309643552333519246284975552905015200802748248167637/78125000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (15841132036981941944020491/2500000000000000000000000)) (.exp (-1629181570843498164928152208326324783980875676161962456793/312500000000000000000000000000000000000000000000000000000) (340202425316060512749/62500000000000000000000) (1088647761011393640797/200000000000000000000000) { parts := 6, inner := (-1629181570843498164928152208326324783980875676161962456793/1875000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (209706987893142736013229409753/500000000000000000000000000000), innerHi := (419413975786285472026458819507/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell557
