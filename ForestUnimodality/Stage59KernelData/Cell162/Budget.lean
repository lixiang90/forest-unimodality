import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell162.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell162
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(99947243167094260935260988339/1000000000000000000000000000000)]
def alpha : ℚ := (43483156993508237685586577121/250000000000000000000000000000)
def D : ℚ := (149250715712991196048958557011/100000000000000000000000000000)
def mlo : ℚ := (4277027027027027027027027027027/250000000000000000000000000000)
def mhi : ℚ := (27563063063063063063063063063063/1000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (487513295782936501807357977448477986830841589120155654377715855140053544150661667861/312500000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (845222122837891554070211/100000000000000000000000)) (.exp (-427477060302504507919055443368828379804238727182136884838153/250000000000000000000000000000000000000000000000000000000000) (180882389404840694884083/1000000000000000000000000) (45220597351210173721021/250000000000000000000000) { parts := 2, inner := (-427477060302504507919055443368828379804238727182136884838153/500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (425302703265380967745291762411/1000000000000000000000000000000), innerHi := (106325675816345241936322940603/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (711126960081574055326764647498898220333906695975358575673003661993458269684877225009/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (845222122837891554070211/100000000000000000000000)) (.exp (-2754852166393917939922801746154682886209890363424986064622357/1000000000000000000000000000000000000000000000000000000000000) (3180921195732172164341/50000000000000000000000) (63618423914643443286821/1000000000000000000000000) { parts := 3, inner := (-918284055464639313307600582051560962069963454474995354874119/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (49900433087980822517063447617/125000000000000000000000000000), innerHi := (399203464703846580136507580937/1000000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck=true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval = budget mhi := by
  norm_num [budgetExpression_hi, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_hi_positive : 0 < budget mhi := by
  rw [← budgetExpression_hi_eval]
  exact budgetExpression_hi.positiveCheck_sound budgetExpression_hi_checked

theorem budget_positive {m : ℝ} (hm : m ∈ Set.Icc (mlo : ℝ) (mhi : ℝ)) :
    0 < budget m := by
  have hs := row.signCheck_sound row_checked
  have hdM : (0 : ℝ) ≤ row.dM := by norm_num [row]
  have hT : ∀ i ∈ row.terms, (0 : ℝ) ≤ row.price i := by
    intro i hi
    exact hs.price i hi
  exact KernelBudget.budget_pos_of_endpoints row.terms row.fixedIndices
    row.A row.B row.dδ row.dM alpha varianceIntercept D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ))
    (fun j => (row.fixedPrice j : ℝ)) (fun j => (countBound j : ℝ))
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage59KernelData.Cell162
