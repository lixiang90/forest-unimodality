import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell379.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell379
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(12140212607874969427167497743/100000000000000000000000000000), (184811219248689921118377568569/1000000000000000000000000000000)]
def R : ℚ := (5091347/6250000)
def D : ℚ := (333003813090909090909090909091/200000000000000000000000000000)
def vmax : ℚ := (90/361)
def mlo : ℚ := (95/2)
def mhi : ℚ := (52777777777777777777777777777777/1000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (6420328775056772584720485618285339400568998904533511248863/76000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (3333829044269029484581779/250000000000000000000000)) (.exp (-230664039549624419116182457117/40000000000000000000000000000) (1565189823615223624389/500000000000000000000000) (3130379647230447248779/1000000000000000000000000) { parts := 6, inner := (-230664039549624419116182457117/240000000000000000000000000000), terms := 40, innerLo := (191235936169118205668010879857/500000000000000000000000000000), innerHi := (76494374467647282267204351943/200000000000000000000000000000) }))) (.mul (.rat (23989472000441935506387381/250000000000000000000000)) (.exp (-3511413165725108501249173802811/400000000000000000000000000000) (77001928199458424209/500000000000000000000000) (154003856398916848419/1000000000000000000000000) { parts := 9, inner := (-1170471055241702833749724600937/1200000000000000000000000000000), terms := 40, innerLo := (94261079314465011552861670371/250000000000000000000000000000), innerHi := (75408863451572009242289336297/200000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (31318394098825482863161384574333587708251306062403052192495454055574274481386811538009161/564062500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (3333829044269029484581779/250000000000000000000000)) (.exp (-640733443193401164211617936436101668723527208357112203057311/100000000000000000000000000000000000000000000000000000000000) (164941527620492483663/100000000000000000000000) (1649415276204924836631/1000000000000000000000000) { parts := 7, inner := (-640733443193401164211617936436101668723527208357112203057311/700000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (200191539979965920008167481589/500000000000000000000000000000), innerHi := (400383079959931840016334963179/1000000000000000000000000000000) }))) (.mul (.rat (23989472000441935506387381/250000000000000000000000)) (.exp (-9753925460347523614581038341141522924607251018950241261891113/1000000000000000000000000000000000000000000000000000000000000) (58066278891007124179/1000000000000000000000000) (2903313944550356209/50000000000000000000000) { parts := 10, inner := (-9753925460347523614581038341141522924607251018950241261891113/10000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (94261079314465011552861670371/250000000000000000000000000000), innerHi := (75408863451572009242289336297/200000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell379
