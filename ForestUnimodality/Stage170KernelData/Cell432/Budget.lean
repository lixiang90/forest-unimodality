import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell432.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell432
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(6268543550698558674211104133/50000000000000000000000000000), (573597907440275304495884267/3906250000000000000000000000)]
def R : ℚ := (8458603/6250000)
def D : ℚ := (63356039/40000000)
def vmax : ℚ := (10/49)
def mlo : ℚ := (595/8)
def mhi : ℚ := (315/4)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (20593368476215298239398832271646503481/44800000000000000000000000000000000000)) (.mul (.rat (31644347456314041444613849/10000000000000000000000000)) (.exp (-745956682533128482231121391827/80000000000000000000000000000) (89215253318927310239/1000000000000000000000000) (557595333243295689/6250000000000000000000) { parts := 10, inner := (-745956682533128482231121391827/800000000000000000000000000000), terms := 40, innerLo := (393589869117352205723025950137/1000000000000000000000000000000), innerHi := (196794934558676102861512975069/500000000000000000000000000000) }))) (.mul (.rat (35024043778940363580431949/10000000000000000000000000)) (.exp (-68258150985392761235010227773/6250000000000000000000000000) (361383121459155787/20000000000000000000000) (18069156072957789351/1000000000000000000000000) { parts := 11, inner := (-68258150985392761235010227773/68750000000000000000000000000), terms := 40, innerLo := (92630187305599320017103976507/250000000000000000000000000000), innerHi := (370520749222397280068415906029/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (10060568197890695564159581330543737137/22400000000000000000000000000000000000)) (.mul (.rat (31644347456314041444613849/10000000000000000000000000)) (.exp (-394918243694009196475299560379/40000000000000000000000000000) (51550116253169013851/1000000000000000000000000) (12887529063292253463/250000000000000000000000) { parts := 10, inner := (-394918243694009196475299560379/400000000000000000000000000000), terms := 40, innerLo := (372582939625155428068153564011/1000000000000000000000000000000), innerHi := (93145734906288857017038391003/250000000000000000000000000000) }))) (.mul (.rat (35024043778940363580431949/10000000000000000000000000)) (.exp (-36136668168737344183240708821/3125000000000000000000000000) (4752304049092493299/500000000000000000000000) (9504608098184986599/1000000000000000000000000) { parts := 12, inner := (-12045556056245781394413569607/12500000000000000000000000000), terms := 40, innerLo := (381499978543663428526169825071/1000000000000000000000000000000), innerHi := (23843748658978964282885614067/62500000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell432
