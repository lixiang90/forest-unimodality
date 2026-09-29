import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell343.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell343
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(122580773559509200964086928243/1000000000000000000000000000000)]
def R : ℚ := (2224285681632653061224489795919/1000000000000000000000000000000)
def D : ℚ := (275490525207547169811320754717/100000000000000000000000000000)
def vmax : ℚ := (1325/6084)
def mlo : ℚ := (24850158538439125631465792042140951/400000000000000000000000000000000)
def mhi : ℚ := (571553646384099889523713216969241873/8000000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (21405212506069300100416332446093422416332408900117734286449561691878407525411431000618674918806667/81120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (83568799229747803281043161/10000000000000000000000000)) (.exp (-3046151656718310581022147354019141551286395896689903458828779093/400000000000000000000000000000000000000000000000000000000000000) (246406900269696782047/500000000000000000000000) (98562760107878712819/200000000000000000000000) { parts := 8, inner := (-3046151656718310581022147354019141551286395896689903458828779093/3200000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (385998269485913105281969651111/1000000000000000000000000000000), innerHi := (48249783685739138160246206389/125000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (8232732447314216988139204432858681805279868737809676413407489295791632613671503468421405437684312843/32448000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (83568799229747803281043161/10000000000000000000000000)) (.exp (-70061488104521143363509389142440255679587105623867779553061919139/8000000000000000000000000000000000000000000000000000000000000000) (157248057867340261511/1000000000000000000000000) (19656007233417532689/125000000000000000000000) { parts := 9, inner := (-70061488104521143363509389142440255679587105623867779553061919139/72000000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (377918685709612170916772647437/1000000000000000000000000000000), innerHi := (188959342854806085458386323719/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell343
