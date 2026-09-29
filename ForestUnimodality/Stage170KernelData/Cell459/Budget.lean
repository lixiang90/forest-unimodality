import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell459.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell459
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(30437851094221116255779745789/250000000000000000000000000000), (185290117495570893415506585283/1000000000000000000000000000000)]
def R : ℚ := (805014379682539682539682539683/1000000000000000000000000000000)
def D : ℚ := (831518150697674418604651162791/500000000000000000000000000000)
def vmax : ℚ := (794745/3189796)
def mlo : ℚ := (45127824019024970273483947681331/1000000000000000000000000000000)
def mhi : ℚ := (95/2)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (158161252944978778381984601684283845363832895702843369763610937947322038231402333034289343847/1993622500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (16573083839334568079237897/2500000000000000000000000)) (.exp (-1373593987697297163730654937047566414496625130699019161165159/250000000000000000000000000000000000000000000000000000000000) (2054910197814480798217/500000000000000000000000) (821964079125792319287/200000000000000000000000) { parts := 6, inner := (-457864662565765721243551645682522138165541710233006387055053/500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (400224625744353423588240987057/1000000000000000000000000000000), innerHi := (200112312872176711794120493529/500000000000000000000000000000) }))) (.mul (.rat (8945732931732699455551483/100000000000000000000000)) (.exp (-8361739814804583034901324230621808504775380839367469258451673/1000000000000000000000000000000000000000000000000000000000000) (116818746993949271993/500000000000000000000000) (233637493987898543987/1000000000000000000000000) { parts := 9, inner := (-8361739814804583034901324230621808504775380839367469258451673/9000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (98728999336430227757067063971/250000000000000000000000000000), innerHi := (78983199469144182205653651177/200000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (342669476957956315307301993096579318161433088303435722973721/5246375000000000000000000000000000000000000000000000000000000)) (.mul (.rat (16573083839334568079237897/2500000000000000000000000)) (.exp (-578319170790201208859815169991/100000000000000000000000000000) (615774569301553974147/200000000000000000000000) (192429552906735616921/62500000000000000000000) { parts := 6, inner := (-192773056930067069619938389997/200000000000000000000000000000), terms := 40, innerLo := (76283150517962628203779806129/200000000000000000000000000000), innerHi := (190707876294906570509449515323/500000000000000000000000000000) }))) (.mul (.rat (8945732931732699455551483/100000000000000000000000)) (.exp (-3520512232415846974894625120377/400000000000000000000000000000) (150540172717391559021/1000000000000000000000000) (75270086358695779511/500000000000000000000000) { parts := 9, inner := (-3520512232415846974894625120377/3600000000000000000000000000000), terms := 40, innerLo := (376092534092652107802219184011/1000000000000000000000000000000), innerHi := (94023133523163026950554796003/250000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell459
