import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell382.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell382
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(15502504885363345333387309491/125000000000000000000000000000), (185372289209416442434215102497/1000000000000000000000000000000)]
def R : ℚ := (25847103/31250000)
def D : ℚ := (410610082127659574468085106383/250000000000000000000000000000)
def vmax : ℚ := (600/2401)
def mlo : ℚ := (735/16)
def mhi : ℚ := (25520833333333333333333333333333/500000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (144833026809187775196414647051944603462901728794003667514159/1960000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (11920582362885198790536379/1000000000000000000000000)) (.exp (-2278868218148411764007934495177/400000000000000000000000000000) (419430765144015588963/125000000000000000000000) (671089224230424942341/200000000000000000000000) { parts := 6, inner := (-759622739382803921335978165059/800000000000000000000000000000), terms := 40, innerLo := (386923444160217468582722931667/1000000000000000000000000000000), innerHi := (96730861040054367145680732917/250000000000000000000000000000) }))) (.mul (.rat (46143269436187026144580159/500000000000000000000000)) (.exp (-27249726513784217037829620067059/3200000000000000000000000000000) (100165502390150581349/500000000000000000000000) (200331004780301162699/1000000000000000000000000) { parts := 9, inner := (-9083242171261405679276540022353/9600000000000000000000000000000), terms := 40, innerLo := (388224670405068781924712552779/1000000000000000000000000000000), innerHi := (19411233520253439096235627639/50000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (1315266936895613334549968741201127005508158254630642613483585163652266628551131635198817797/30012500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (11920582362885198790536379/1000000000000000000000000)) (.exp (-395636843428543709029155294301557332498371545551555537563503/62500000000000000000000000000000000000000000000000000000000) (1781696114860663918363/1000000000000000000000000) (445424028715165979591/250000000000000000000000) { parts := 7, inner := (-395636843428543709029155294301557332498371545551555537563503/437500000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (404819987910139765689730788637/1000000000000000000000000000000), innerHi := (202409993955069882844865394319/500000000000000000000000000000) }))) (.mul (.rat (46143269436187026144580159/500000000000000000000000)) (.exp (-4730855297531982124623197928308792375903596861185855261632501/500000000000000000000000000000000000000000000000000000000000) (77773438302748677477/1000000000000000000000000) (38886719151374338739/500000000000000000000000) { parts := 10, inner := (-4730855297531982124623197928308792375903596861185855261632501/5000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (388224670405068781924712552779/1000000000000000000000000000000), innerHi := (19411233520253439096235627639/50000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell382
