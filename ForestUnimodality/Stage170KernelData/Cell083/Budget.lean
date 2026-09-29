import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell083.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell083
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(76002269852598642719461437021/1000000000000000000000000000000), (178261067662069514939774026281/1000000000000000000000000000000)]
def R : ℚ := (74081147/50000000)
def D : ℚ := (2258214870770100857762277311717/1000000000000000000000000000000)
def vmax : ℚ := (70/289)
def mlo : ℚ := (3398069285714285714285714285714245737/32000000000000000000000000000000000)
def mhi : ℚ := (425/4)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (10765868260590217566666074119740390248141623728351677849606715955768180463849099951263845277336589521/29593600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (83192247896267161877403851/10000000000000000000000000)) (.exp (-258260978830684260866689811396919988064114596991888963313143229477/32000000000000000000000000000000000000000000000000000000000000000) (312578291158363174557/1000000000000000000000000) (156289145579181587279/500000000000000000000000) { parts := 9, inner := (-28695664314520473429632201266324443118234955221320995923682581053/32000000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (203948719775167941456011607653/500000000000000000000000000000), innerHi := (407897439550335882912023215307/1000000000000000000000000000000) }))) (.mul (.rat (2009115350527560650562009/100000000000000000000000)) (.exp (-605743458861114512296030111360366057177794911257838534099530214097/32000000000000000000000000000000000000000000000000000000000000000) (6012151959103301/1000000000000000000000000) (3006075979551651/500000000000000000000000) { parts := 19, inner := (-605743458861114512296030111360366057177794911257838534099530214097/608000000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (23077958236167306967786856943/62500000000000000000000000000), innerHi := (369247331778676911484589711089/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (98928798896000249060529037264620960394497846815655603852453/272000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (83192247896267161877403851/10000000000000000000000000)) (.exp (-1292038587494176926230844429357/160000000000000000000000000000) (311148218705712710893/1000000000000000000000000) (155574109352856355447/500000000000000000000000) { parts := 9, inner := (-143559843054908547358982714373/160000000000000000000000000000), terms := 40, innerLo := (3185075507515531856926781859/7812500000000000000000000000), innerHi := (407689664961988077686628077953/1000000000000000000000000000000) }))) (.mul (.rat (2009115350527560650562009/100000000000000000000000)) (.exp (-3030438150255181753976158446777/160000000000000000000000000000) (2973917827295507/500000000000000000000000) (1189567130918203/200000000000000000000000) { parts := 19, inner := (-3030438150255181753976158446777/3040000000000000000000000000000), terms := 40, innerLo := (369038370708000950641877746701/1000000000000000000000000000000), innerHi := (184519185354000475320938873351/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell083
