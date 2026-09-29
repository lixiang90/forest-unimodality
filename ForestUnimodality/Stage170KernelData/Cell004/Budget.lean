import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell004.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell004
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(188461072002779512287804599/1600000000000000000000000000)]
def R : ℚ := (256966306796116504854368932039/200000000000000000000000000000)
def D : ℚ := (747246585829072315558802045289/500000000000000000000000000000)
def vmax : ℚ := (3811/19600)
def mlo : ℚ := (47297297297297297297297297297297/500000000000000000000000000000)
def mhi : ℚ := (1087837837837837837837837837837831/10000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (23039649936873207133701858655525058376987118555590701469613841911369615020196151007612767281/49000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (2902269144265310796271251/250000000000000000000000)) (.exp (-8913699351482814770369136439189133160221837011496346868903/800000000000000000000000000000000000000000000000000000000) (7244475569936680521/500000000000000000000000) (14488951139873361043/1000000000000000000000000) { parts := 12, inner := (-8913699351482814770369136439189133160221837011496346868903/9600000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (197570947821447172436352708879/500000000000000000000000000000), innerHi := (395141895642894344872705417759/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (1097820378605558808404487052723440822530223866805004590498393486412677879351009180747886255211/2450000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (2902269144265310796271251/250000000000000000000000)) (.exp (-205015085084104739718490138101350062685102251264415977984769/16000000000000000000000000000000000000000000000000000000000) (34048854302167103/12500000000000000000000) (2723908344173368241/1000000000000000000000000) { parts := 13, inner := (-205015085084104739718490138101350062685102251264415977984769/208000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (186598388247448101116228920697/500000000000000000000000000000), innerHi := (74639355298979240446491568279/200000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell004
