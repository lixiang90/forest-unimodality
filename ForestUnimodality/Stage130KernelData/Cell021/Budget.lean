import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage130KernelData.Cell021.Parameters

namespace ForestUnimodality.Stage130KernelData.Cell021
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(54196053821580075285822330313/500000000000000000000000000000), (11068491252079253530389190021/50000000000000000000000000000)]
def R : ℚ := (9850373/10000000)
def D : ℚ := (90810693/50000000)
def vmax : ℚ := (5696/23409)
def mlo : ℚ := (5049/128)
def mhi : ℚ := (13005/256)
def alpha : ℚ := (876683197/3657656250)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (1295690277758939512773019382264764378041/2720000000000000000000000000000000000000)) (.mul (.rat (34128399190516600647526957/10000000000000000000000000)) (.exp (-273635875745157800118116945750337/64000000000000000000000000000000) (3476063096719613693611/250000000000000000000000) (2780850477375690954889/200000000000000000000000) { parts := 5, inner := (-273635875745157800118116945750337/320000000000000000000000000000000), terms := 40, innerLo := (212617757265900660752721313393/500000000000000000000000000000), innerHi := (425235514531801321505442626787/1000000000000000000000000000000) }))) (.mul (.rat (16875249413925526908997199/1000000000000000000000000)) (.exp (-55884812331748151074935020416029/6400000000000000000000000000000) (80669571774105633777/500000000000000000000000) (32267828709642253511/200000000000000000000000) { parts := 9, inner := (-6209423592416461230548335601781/6400000000000000000000000000000), terms := 40, innerLo := (378998725646720497131227152553/1000000000000000000000000000000), innerHi := (189499362823360248565613576277/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (338119675181714933503185803925090917299/768000000000000000000000000000000000000)) (.mul (.rat (34128399190516600647526957/10000000000000000000000000)) (.exp (-140963935989929775818423881144113/25600000000000000000000000000000) (126896387314713410183/31250000000000000000000) (4060684394070829125857/1000000000000000000000000) { parts := 6, inner := (-46987978663309925272807960381371/51200000000000000000000000000000), terms := 40, innerLo := (199711562911351759190915032699/500000000000000000000000000000), innerHi := (399423125822703518381830065399/1000000000000000000000000000000) }))) (.mul (.rat (16875249413925526908997199/1000000000000000000000000)) (.exp (-28789145746658138432542283244621/2560000000000000000000000000000) (2612512986641527747/200000000000000000000000) (816410308325477421/62500000000000000000000) { parts := 12, inner := (-9596381915552712810847427748207/10240000000000000000000000000000), terms := 40, innerLo := (391744016575800680592832217671/1000000000000000000000000000000), innerHi := (48968002071975085074104027209/125000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck = true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mhi := by
  norm_num [budgetExpression_hi, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_hi_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mhi := by
  rw [← budgetExpression_hi_eval]
  exact budgetExpression_hi.positiveCheck_sound budgetExpression_hi_checked

theorem budget_positive {m : ℝ} (hm : m ∈ Set.Icc (mlo : ℝ) (mhi : ℝ)) :
    0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D m := by
  have hs := row.signCheck_sound row_checked
  have hdM : (0 : ℝ) ≤ row.dM := by norm_num [row]
  have hT : ∀ i ∈ row.terms, (0 : ℝ) ≤ row.price i := by
    intro i hi
    exact hs.price i hi
  exact KernelBudget.budget_pos_of_endpoints row.terms (∅ : Finset ℤ)
    row.A row.B row.dδ row.dM alpha varianceIntercept D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ)) (fun _ => 0) (fun _ => 0)
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage130KernelData.Cell021
