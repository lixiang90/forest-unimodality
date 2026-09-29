import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell099.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell099
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(39784665452232470875358119623/500000000000000000000000000000), (88554163184708664660182779787/500000000000000000000000000000)]
def R : ℚ := (527141393604651162790697674419/500000000000000000000000000000)
def D : ℚ := (177911323/100000000)
def vmax : ℚ := (5762/23409)
def mlo : ℚ := (694608582089552238805970149253724261/8000000000000000000000000000000000)
def mhi : ℚ := (1575/16)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (23691133527151529825778196321362437371448429213948912800320113514755038768638375158177105092746509713/55488000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (89257385417541765804116949/10000000000000000000000000)) (.exp (-27634770058682391190482754829221835024761824847963395838695273603/4000000000000000000000000000000000000000000000000000000000000000) (499531601689863139551/500000000000000000000000) (999063203379726279103/1000000000000000000000000) { parts := 7, inner := (-27634770058682391190482754829221835024761824847963395838695273603/28000000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (372709466317287438237871068629/1000000000000000000000000000000), innerHi := (37270946631728743823787106863/100000000000000000000000000000) }))) (.mul (.rat (3829231967311184092750409/125000000000000000000000)) (.exp (-61510481727857313211502952945995506043259175139364270189382312407/4000000000000000000000000000000000000000000000000000000000000000) (209693177956432661/1000000000000000000000000) (104846588978216331/500000000000000000000000) { parts := 16, inner := (-61510481727857313211502952945995506043259175139364270189382312407/64000000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (191235723475161733411630285653/500000000000000000000000000000), innerHi := (382471446950323466823260571307/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (9677546461688651395899455641745466536894854859757051033393/23120000000000000000000000000000000000000000000000000000000)) (.mul (.rat (89257385417541765804116949/10000000000000000000000000)) (.exp (-2506433923490645665147561536249/320000000000000000000000000000) (24786913310869787513/62500000000000000000000) (396590612973916600209/1000000000000000000000000) { parts := 8, inner := (-2506433923490645665147561536249/2560000000000000000000000000000), terms := 40, innerLo := (375658139974201404707182070791/1000000000000000000000000000000), innerHi := (46957267496775175588397758849/125000000000000000000000000000) }))) (.mul (.rat (3829231967311184092750409/125000000000000000000000)) (.exp (-5578912280636645873591515126581/320000000000000000000000000000) (26820458145925161/1000000000000000000000000) (13410229072962581/500000000000000000000000) { parts := 18, inner := (-619879142292960652621279458509/640000000000000000000000000000), terms := 40, innerLo := (379628870594032846777758531321/1000000000000000000000000000000), innerHi := (189814435297016423388879265661/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell099
