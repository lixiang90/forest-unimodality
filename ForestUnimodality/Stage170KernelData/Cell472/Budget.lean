import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell472.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell472
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(4997060665547122769931912021/40000000000000000000000000000), (183669383518134747765020627797/1000000000000000000000000000000)]
def R : ℚ := (6425080953727506426735218509/7812500000000000000000000000)
def D : ℚ := (327794435461887281364716044051/200000000000000000000000000000)
def vmax : ℚ := (90316075/361456144)
def mlo : ℚ := (11038118994474807848391896995571/250000000000000000000000000000)
def mhi : ℚ := (735/16)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (15462771233769695110153299023816236320191589668580556081353188742783614479179317033808091/259929687500000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (4407394360359367380119977/1250000000000000000000000)) (.exp (-55158150248918620871727540332234136211676140585265398658991/10000000000000000000000000000000000000000000000000000000000) (804529488849067296519/200000000000000000000000) (1005661861061334120649/250000000000000000000000) { parts := 6, inner := (-18386050082972873623909180110744712070558713528421799552997/20000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (199398551712374182046997862483/500000000000000000000000000000), innerHi := (398797103424748364093995724967/1000000000000000000000000000000) }))) (.mul (.rat (89402308324360802771479939/1000000000000000000000000)) (.exp (-2027364510915001367560184948627337083820952041976484548487087/250000000000000000000000000000000000000000000000000000000000) (75170446360409429183/250000000000000000000000) (300681785441637716733/1000000000000000000000000) { parts := 9, inner := (-2027364510915001367560184948627337083820952041976484548487087/2250000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (101535655663726110481517222833/250000000000000000000000000000), innerHi := (406142622654904441926068891333/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (41758232223271697808597528607604410827778408665892953767/848750000000000000000000000000000000000000000000000000000)) (.mul (.rat (4407394360359367380119977/1250000000000000000000000)) (.exp (-734567917835427047179991067087/128000000000000000000000000000) (643718029248189517179/200000000000000000000000) (402323768280118448237/125000000000000000000000) { parts := 6, inner := (-244855972611809015726663689029/256000000000000000000000000000), terms := 40, innerLo := (192123703842387951860839908933/500000000000000000000000000000), innerHi := (384247407684775903721679817867/1000000000000000000000000000000) }))) (.mul (.rat (89402308324360802771479939/1000000000000000000000000)) (.exp (-26999399377165807921458032286159/3200000000000000000000000000000) (54157902038001580809/250000000000000000000000) (216631608152006323237/1000000000000000000000000) { parts := 9, inner := (-8999799792388602640486010762053/9600000000000000000000000000000), terms := 40, innerLo := (78322758736290468089528291287/200000000000000000000000000000), innerHi := (97903448420363085111910364109/250000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell472
