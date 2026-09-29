import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell101.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell101
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(114970320366271622228626960681/1000000000000000000000000000000), (179298536061889179706434124893/1000000000000000000000000000000)]
def R : ℚ := (53922541/50000000)
def D : ℚ := (883742337164179104477611940299/500000000000000000000000000000)
def vmax : ℚ := (20/81)
def mlo : ℚ := (1035/16)
def mhi : ℚ := (4761/64)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (261191226587340683803845206606032767330619238127367185277733/720000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (7595993942470545157163997/500000000000000000000000)) (.exp (-23798856315818225801325780860967/3200000000000000000000000000000) (117793141367647885719/200000000000000000000000) (147241426709559857149/250000000000000000000000) { parts := 8, inner := (-23798856315818225801325780860967/25600000000000000000000000000000), terms := 40, innerLo := (197347330163983527398264167783/500000000000000000000000000000), innerHi := (394694660327967054796528335567/1000000000000000000000000000000) }))) (.mul (.rat (1448665841658077768627777/62500000000000000000000)) (.exp (-37114796964811060199231863852851/3200000000000000000000000000000) (9181003445623105287/1000000000000000000000000) (1147625430702888161/125000000000000000000000) { parts := 12, inner := (-12371598988270353399743954617617/12800000000000000000000000000000), terms := 40, innerLo := (380400295704922417483164599831/1000000000000000000000000000000), innerHi := (47550036963115302185395574979/125000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (5134679356677940936144555558797042711104242476929445261387859/14400000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (7595993942470545157163997/500000000000000000000000)) (.exp (-547373695263819193430492959802241/64000000000000000000000000000000) (193020532540619479187/1000000000000000000000000) (48255133135154869797/250000000000000000000000) { parts := 9, inner := (-60819299473757688158943662200249/64000000000000000000000000000000), terms := 40, innerLo := (19331220881349220291607224853/50000000000000000000000000000), innerHi := (386624417626984405832144497061/1000000000000000000000000000000) }))) (.mul (.rat (1448665841658077768627777/62500000000000000000000)) (.exp (-853640330190654384582332868615573/64000000000000000000000000000000) (80592323590436499/50000000000000000000000) (1611846471808729981/1000000000000000000000000) { parts := 14, inner := (-853640330190654384582332868615573/896000000000000000000000000000000), terms := 40, innerLo := (77137827071313188277810878459/200000000000000000000000000000), innerHi := (48211141919570742673631799037/125000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell101
