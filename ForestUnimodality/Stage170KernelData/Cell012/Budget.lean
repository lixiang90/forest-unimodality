import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell012.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell012
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(24568660801978636143221469313/200000000000000000000000000000)]
def R : ℚ := (332518930693069306930693069307/250000000000000000000000000000)
def D : ℚ := (1557844460223537146614069690993/1000000000000000000000000000000)
def vmax : ℚ := (3939/19600)
def mlo : ℚ := (89743589743589743589743589743589/1000000000000000000000000000000)
def mhi : ℚ := (2064102564102564102564102564102547/20000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (11109918043579403113140443643125408427212240086715033723353411465874385703463247693027772473/24500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (89675057378708835642555641/10000000000000000000000000)) (.exp (-2204879815562185294904490835782033013047095964603893501984357/200000000000000000000000000000000000000000000000000000000000) (3259825178518132331/200000000000000000000000) (2037390736573832707/125000000000000000000000) { parts := 12, inner := (-2204879815562185294904490835782033013047095964603893501984357/2400000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (399037483398151665441935610897/1000000000000000000000000000000), innerHi := (199518741699075832720967805449/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (8456207341537671161023895198162873364510957776932340242335005150090097984077853455847310228953/19600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (89675057378708835642555641/10000000000000000000000000)) (.exp (-50712235757930261782803289222986759300083207185889550545640211/4000000000000000000000000000000000000000000000000000000000000) (1559405155429210239/500000000000000000000000) (3118810310858420479/1000000000000000000000000) { parts := 13, inner := (-50712235757930261782803289222986759300083207185889550545640211/52000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (377103609498068386133394381331/1000000000000000000000000000000), innerHi := (94275902374517096533348595333/250000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck = true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mhi := by
  norm_num [budgetExpression_hi, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

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
end ForestUnimodality.Stage170KernelData.Cell012
