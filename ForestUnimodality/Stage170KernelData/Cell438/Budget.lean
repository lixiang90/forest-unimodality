import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell438.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell438
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(151002989960658591337891111153/1000000000000000000000000000000), (157890428037506160057480231943/1000000000000000000000000000000)]
def R : ℚ := (3803687/2500000)
def D : ℚ := (3383039/2000000)
def vmax : ℚ := (2/9)
def mlo : ℚ := (255/4)
def mhi : ℚ := (135/2)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (187295657672454089425563865329766297/480000000000000000000000000000000000)) (.mul (.rat (1342865367432518330925717/312500000000000000000000)) (.exp (-7701152487993588158232446668803/800000000000000000000000000000) (32980707437851120223/500000000000000000000000) (65961414875702240447/1000000000000000000000000) { parts := 10, inner := (-7701152487993588158232446668803/8000000000000000000000000000000), terms := 40, innerLo := (381881831062893991966670154869/1000000000000000000000000000000), innerHi := (38188183106289399196667015487/100000000000000000000000000000) }))) (.mul (.rat (50876535748303943762493873/10000000000000000000000000)) (.exp (-8052411829912814162931491829093/800000000000000000000000000000) (5315112770080214287/125000000000000000000000) (42520902160641714297/1000000000000000000000000) { parts := 11, inner := (-8052411829912814162931491829093/8800000000000000000000000000000), terms := 40, innerLo := (400497882810403839719045561529/1000000000000000000000000000000), innerHi := (40049788281040383971904556153/100000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (30487854263123178714159771796870523/80000000000000000000000000000000000)) (.mul (.rat (1342865367432518330925717/312500000000000000000000)) (.exp (-4077080728937781966123060001131/400000000000000000000000000000) (37442586594695558963/1000000000000000000000000) (9360646648673889741/250000000000000000000000) { parts := 11, inner := (-4077080728937781966123060001131/4400000000000000000000000000000), terms := 40, innerLo := (39589381145567981450813939429/100000000000000000000000000000), innerHi := (395893811455679814508139394291/1000000000000000000000000000000) }))) (.mul (.rat (50876535748303943762493873/10000000000000000000000000)) (.exp (-4263041557012666321551966262461/400000000000000000000000000000) (4704261278715821323/200000000000000000000000) (2940163299197388327/125000000000000000000000) { parts := 11, inner := (-4263041557012666321551966262461/4400000000000000000000000000000), terms := 40, innerLo := (379510474726792068798914891361/1000000000000000000000000000000), innerHi := (189755237363396034399457445681/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell438
