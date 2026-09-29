import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell051.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell051
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(46643567705920195128416617789/500000000000000000000000000000), (7834225203999927746296684029/50000000000000000000000000000)]
def R : ℚ := (1242430367469879518072289156627/1000000000000000000000000000000)
def D : ℚ := (23594116099881093935790725327/10000000000000000000000000000)
def vmax : ℚ := (14774/65025)
def mlo : ℚ := (37891853932584269662921348314606379/400000000000000000000000000000000)
def mhi : ℚ := (425/4)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (21098608762863378368875259195107092592778398628179342768225370180489847027628420427767894015497253/46240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (19147698967840420802843937/2500000000000000000000000)) (.exp (-1767411254407332787035887544001992919760828063609251698024276031/200000000000000000000000000000000000000000000000000000000000000) (29049938710246531413/200000000000000000000000) (72624846775616328533/500000000000000000000000) { parts := 9, inner := (-1767411254407332787035887544001992919760828063609251698024276031/1800000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (187300252412157220551370194537/500000000000000000000000000000), innerHi := (14984020192972577644109615563/40000000000000000000000000000) }))) (.mul (.rat (7641968707693225226762479/1250000000000000000000000)) (.exp (-296853317104935464420418874183130586487493169958781514070820991/20000000000000000000000000000000000000000000000000000000000000) (358023985120455857/1000000000000000000000000) (179011992560227929/500000000000000000000000) { parts := 15, inner := (-98951105701645154806806291394376862162497723319593838023606997/100000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (371758415260746468474250394689/1000000000000000000000000000000), innerHi := (37175841526074646847425039469/100000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (59215907418075691971886888248809973852090247456821987204731/136000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (19147698967840420802843937/2500000000000000000000000)) (.exp (-792940651000643317183082502413/80000000000000000000000000000) (24794088055559720949/500000000000000000000000) (49588176111119441899/1000000000000000000000000) { parts := 10, inner := (-792940651000643317183082502413/800000000000000000000000000000), terms := 40, innerLo := (74228008559612714321172157261/200000000000000000000000000000), innerHi := (185570021399031785802930393153/500000000000000000000000000000) }))) (.mul (.rat (7641968707693225226762479/1250000000000000000000000)) (.exp (-133181828467998771687043628493/8000000000000000000000000000) (11776421635757599/200000000000000000000000) (14720527044696999/250000000000000000000000) { parts := 17, inner := (-7834225203999927746296684029/8000000000000000000000000000), terms := 40, innerLo := (375582114785043244580642075967/1000000000000000000000000000000), innerHi := (5868470543516300696572532437/15625000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell051
