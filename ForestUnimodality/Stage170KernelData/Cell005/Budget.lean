import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell005.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell005
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(188461072002779512287804599/1600000000000000000000000000)]
def R : ℚ := (256966306796116504854368932039/200000000000000000000000000000)
def D : ℚ := (747246585829072315558802045289/500000000000000000000000000000)
def vmax : ℚ := (3811/19600)
def mlo : ℚ := (1087837837837837837837837837837831/10000000000000000000000000000000)
def mhi : ℚ := (25020270270270270270270270270270113/200000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (332521687751546215481261172200218905604038511894486311244228827380082664387372975480601464129/700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (58678397803153323764036031/1000000000000000000000000)) (.exp (-205015085084104739718490138101350062685102251264415977984769/16000000000000000000000000000000000000000000000000000000000) (34048854302167103/12500000000000000000000) (2723908344173368241/1000000000000000000000000) { parts := 13, inner := (-205015085084104739718490138101350062685102251264415977984769/208000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (186598388247448101116228920697/500000000000000000000000000000), innerHi := (74639355298979240446491568279/200000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (31614593649283801822119175257878868947470012459302163961762679676641252525578195125419834742909/70000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (58678397803153323764036031/1000000000000000000000000)) (.exp (-4715346956934409013525273176331051441757351779081567493649687/320000000000000000000000000000000000000000000000000000000000) (3188315941022359/8000000000000000000000) (99634873156948719/250000000000000000000000) { parts := 15, inner := (-4715346956934409013525273176331051441757351779081567493649687/4800000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (374424930260483105968598250849/1000000000000000000000000000000), innerHi := (7488498605209662119371965017/20000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell005
