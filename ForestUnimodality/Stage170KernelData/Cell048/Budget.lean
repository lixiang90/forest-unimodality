import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell048.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell048
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(91270153977580735993702224297/1000000000000000000000000000000), (19248429204029960615525454671/125000000000000000000000000000)]
def R : ℚ := (607867383928571428571428571429/500000000000000000000000000000)
def D : ℚ := (5928031/2500000)
def vmax : ℚ := (1624/7225)
def mlo : ℚ := (38762931034482758620689655172413483/400000000000000000000000000000000)
def mhi : ℚ := (425/4)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (1264057002117143995770764366160780494097808232350452321863359337861230775201823640269002802422593/2720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (27143570583282525809920571/5000000000000000000000000)) (.exp (-3537898684139584305135190099581527731293285504015214090892996451/400000000000000000000000000000000000000000000000000000000000000) (28827388798654393233/200000000000000000000000) (72068471996635983083/500000000000000000000000) { parts := 9, inner := (-393099853793287145015021122175725303477031722668357121210332939/400000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (374280547980458097796657477849/1000000000000000000000000000000), innerHi := (7485610959609161955933149557/20000000000000000000000000000) }))) (.mul (.rat (73615788347813557734866663/10000000000000000000000000)) (.exp (-746125533757937223342329370070265582719867867536696019985729093/50000000000000000000000000000000000000000000000000000000000000) (16527454185967033/50000000000000000000000) (330549083719340661/1000000000000000000000000) { parts := 15, inner := (-746125533757937223342329370070265582719867867536696019985729093/750000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (14791392283438187393707550643/40000000000000000000000000000), innerHi := (92446201771488671210672191519/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (950645701694883170326914134499099872711639934980548949371/2125000000000000000000000000000000000000000000000000000000)) (.mul (.rat (27143570583282525809920571/5000000000000000000000000)) (.exp (-1551592617618872511892937813049/160000000000000000000000000000) (3071986510898824931/50000000000000000000000) (61439730217976498621/1000000000000000000000000) { parts := 10, inner := (-1551592617618872511892937813049/1600000000000000000000000000000), terms := 40, innerLo := (37917957023628524252069047051/100000000000000000000000000000), innerHi := (379179570236285242520690470511/1000000000000000000000000000000) }))) (.mul (.rat (73615788347813557734866663/10000000000000000000000000)) (.exp (-327223296468509330463932729407/20000000000000000000000000000) (19605431641307393/250000000000000000000000) (78421726565229573/1000000000000000000000000) { parts := 17, inner := (-19248429204029960615525454671/20000000000000000000000000000), terms := 40, innerLo := (381966847725153278056444172099/1000000000000000000000000000000), innerHi := (3819668477251532780564441721/10000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell048
