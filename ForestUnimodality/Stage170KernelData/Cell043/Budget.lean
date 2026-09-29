import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell043.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell043
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(46239187831222106141576878737/500000000000000000000000000000), (80919565799564405573810731613/500000000000000000000000000000)]
def R : ℚ := (3803687/2500000)
def D : ℚ := (3383039/2000000)
def vmax : ℚ := (2/9)
def mlo : ℚ := (1587/16)
def mhi : ℚ := (36501/320)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (1176493531491963553729895147772980893/3000000000000000000000000000000000000)) (.mul (.rat (17076689577232682104579453/5000000000000000000000000)) (.exp (-73381591088149482446682506555619/8000000000000000000000000000000) (51917944994620742571/500000000000000000000000) (103835889989241485143/1000000000000000000000000) { parts := 10, inner := (-73381591088149482446682506555619/80000000000000000000000000000000), terms := 40, innerLo := (399608528995925119177735153539/1000000000000000000000000000000), innerHi := (19980426449796255958886757677/50000000000000000000000000000) }))) (.mul (.rat (87030218780064281247632607/10000000000000000000000000)) (.exp (-128419350923908711645637631069831/8000000000000000000000000000000) (106788150656093059/1000000000000000000000000) (5339407532804653/50000000000000000000000) { parts := 17, inner := (-128419350923908711645637631069831/136000000000000000000000000000000), terms := 40, innerLo := (77793465237810239569038190837/200000000000000000000000000000), innerHi := (194483663094525598922595477093/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (22339753647142807640424570393989816789/60000000000000000000000000000000000000)) (.mul (.rat (17076689577232682104579453/5000000000000000000000000)) (.exp (-1687776595027438096273697650779237/160000000000000000000000000000000) (13115039937386716417/500000000000000000000000) (5246015974954686567/200000000000000000000000) { parts := 11, inner := (-1687776595027438096273697650779237/1760000000000000000000000000000000), terms := 40, innerLo := (76657955669741586771318341089/200000000000000000000000000000), innerHi := (191644889174353966928295852723/500000000000000000000000000000) }))) (.mul (.rat (87030218780064281247632607/10000000000000000000000000)) (.exp (-2953645071249900367849665514606113/160000000000000000000000000000000) (4805864586899781/500000000000000000000000) (9611729173799563/1000000000000000000000000) { parts := 19, inner := (-2953645071249900367849665514606113/3040000000000000000000000000000000), terms := 40, innerLo := (378479346828021846283111678313/1000000000000000000000000000000), innerHi := (189239673414010923141555839157/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell043
