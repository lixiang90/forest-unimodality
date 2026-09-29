import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell041.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell041
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(46239187831222106141576878737/500000000000000000000000000000), (80919565799564405573810731613/500000000000000000000000000000)]
def R : ℚ := (3803687/2500000)
def D : ℚ := (3383039/2000000)
def vmax : ℚ := (2/9)
def mlo : ℚ := (75/1)
def mhi : ℚ := (345/4)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (94229318343229810733558436039972451/240000000000000000000000000000000000)) (.mul (.rat (11259320188373380666746471/10000000000000000000000000)) (.exp (-138717563493666318424730636211/20000000000000000000000000000) (15191701121780506697/15625000000000000000000) (972268871793952428609/1000000000000000000000000) { parts := 7, inner := (-19816794784809474060675805173/20000000000000000000000000000), terms := 40, innerLo := (185632397233982476923992054969/500000000000000000000000000000), innerHi := (371264794467964953847984109939/1000000000000000000000000000000) }))) (.mul (.rat (23287020468651369320411959/2500000000000000000000000)) (.exp (-242758697398693216721432194839/20000000000000000000000000000) (5352563944279657373/1000000000000000000000000) (2676281972139828687/500000000000000000000000) { parts := 13, inner := (-242758697398693216721432194839/260000000000000000000000000000), terms := 40, innerLo := (196550776151349329521287170921/500000000000000000000000000000), innerHi := (393101552302698659042574341843/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (1792828963324019332730758103126866373/4800000000000000000000000000000000000)) (.mul (.rat (11259320188373380666746471/10000000000000000000000000)) (.exp (-3190503960354325323768804632853/400000000000000000000000000000) (343521828543960107113/1000000000000000000000000) (171760914271980053557/500000000000000000000000) { parts := 8, inner := (-3190503960354325323768804632853/3200000000000000000000000000000), terms := 40, innerLo := (36897274937137411690323875349/100000000000000000000000000000), innerHi := (368972749371374116903238753491/1000000000000000000000000000000) }))) (.mul (.rat (23287020468651369320411959/2500000000000000000000000)) (.exp (-5583450040169943984592940481297/400000000000000000000000000000) (5416592465233711/6250000000000000000000) (866654794437393761/1000000000000000000000000) { parts := 14, inner := (-5583450040169943984592940481297/5600000000000000000000000000000), terms := 40, innerLo := (368968261797257676430579365513/1000000000000000000000000000000), innerHi := (184484130898628838215289682757/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell041
