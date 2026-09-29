import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell473.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell473
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(62705986527508938676679987227/500000000000000000000000000000), (1889069023004041119031866029/10000000000000000000000000000)]
def R : ℚ := (25847103/31250000)
def D : ℚ := (204656513220630989555292344137/125000000000000000000000000000)
def vmax : ℚ := (600/2401)
def mlo : ℚ := (11111570900536368041348121029389/250000000000000000000000000000)
def mhi : ℚ := (735/16)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (1098473867722156907652492953380044548075751452723991464299349676129038472544417736376897163/15006250000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (9555735708549875084827363/1000000000000000000000000)) (.exp (-696762015188493859664243489310714048730875724909398611614303/125000000000000000000000000000000000000000000000000000000000) (118590755145562752671/31250000000000000000000) (3794904164658008085473/1000000000000000000000000) { parts := 6, inner := (-696762015188493859664243489310714048730875724909398611614303/750000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (197471067150835997269076504671/500000000000000000000000000000), innerHi := (394942134301671994538153009343/1000000000000000000000000000000) }))) (.mul (.rat (41885680922456586472435447/500000000000000000000000)) (.exp (-20990524385116370132478004863508565214013435870109019726281/2500000000000000000000000000000000000000000000000000000000) (56430310976248140503/250000000000000000000000) (225721243904992562013/1000000000000000000000000) { parts := 9, inner := (-20990524385116370132478004863508565214013435870109019726281/22500000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (98351591132262842428537229533/250000000000000000000000000000), innerHi := (393406364529051369714148918133/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (127815672993520553672393979452174678263256071076711979959699/1960000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (9555735708549875084827363/1000000000000000000000000)) (.exp (-9217780019543813985471958122369/1600000000000000000000000000000) (3147607897617065861193/1000000000000000000000000) (1573803948808532930597/500000000000000000000000) { parts := 6, inner := (-3072593339847937995157319374123/3200000000000000000000000000000), terms := 40, innerLo := (47852737131818201372102255831/125000000000000000000000000000), innerHi := (382821897054545610976818046649/1000000000000000000000000000000) }))) (.mul (.rat (41885680922456586472435447/500000000000000000000000)) (.exp (-277693146381594044497684306263/32000000000000000000000000000) (42576624091426053991/250000000000000000000000) (34061299273140843193/200000000000000000000000) { parts := 9, inner := (-92564382127198014832561435421/96000000000000000000000000000), terms := 40, innerLo := (47660426645018167716128527983/125000000000000000000000000000), innerHi := (76256682632029068345805644773/200000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell473
