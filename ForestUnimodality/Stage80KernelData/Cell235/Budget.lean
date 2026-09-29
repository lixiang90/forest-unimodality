import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage80KernelData.Cell235.Parameters

namespace ForestUnimodality.Stage80KernelData.Cell235
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(149572838702056300286120170989/1000000000000000000000000000000), (40167789076847666164372307767/250000000000000000000000000000)]
def R : ℚ := (19664583/10000000)
def D : ℚ := (342313033551401869158878504673/125000000000000000000000000000)
def vmax : ℚ := (5243/24336)
def mlo : ℚ := (39/2)
def mhi : ℚ := (23833333333333333333333333333333/1000000000000000000000000000000)
def alpha : ℚ := (34367136223/81120000000)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (21508274582109623663944505524882331506765014011248381786713/65000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (34956549717003264632353421/10000000000000000000000000)) (.exp (-5833340709380195711158686668571/2000000000000000000000000000000) (10822713330070366794531/200000000000000000000000) (3382097915646989623291/62500000000000000000000) { parts := 3, inner := (-1944446903126731903719562222857/2000000000000000000000000000000), terms := 40, innerLo := (94560275419742797861010346613/250000000000000000000000000000), innerHi := (378241101678971191444041386453/1000000000000000000000000000000) }))) (.mul (.rat (12961365940378402061838869/10000000000000000000000000)) (.exp (-1566543773997058980410520002913/500000000000000000000000000000) (10895756155271326532817/250000000000000000000000) (43583024621085306131269/1000000000000000000000000) { parts := 4, inner := (-1566543773997058980410520002913/2000000000000000000000000000000), terms := 40, innerLo := (456908609637148244171677046183/1000000000000000000000000000000), innerHi := (57113576204643530521459630773/125000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (881836504963790174466276828158818933432408278988050478309806160038803107383165771057439347/3380000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (34956549717003264632353421/10000000000000000000000000)) (.exp (-3564819322399008490152530741904450142387099314566571293276337/1000000000000000000000000000000000000000000000000000000000000) (7075524644384059052157/250000000000000000000000) (28302098577536236208629/1000000000000000000000000) { parts := 4, inner := (-3564819322399008490152530741904450142387099314566571293276337/4000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (410161280073187917124008688217/1000000000000000000000000000000), innerHi := (205080640036593958562004344109/500000000000000000000000000000) }))) (.mul (.rat (12961365940378402061838869/10000000000000000000000000)) (.exp (-957332306331536043584206668446819944070307717444611875897411/250000000000000000000000000000000000000000000000000000000000) (10862091387641069672469/500000000000000000000000) (21724182775282139344939/1000000000000000000000000) { parts := 4, inner := (-957332306331536043584206668446819944070307717444611875897411/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (191957845280406551340723629161/500000000000000000000000000000), innerHi := (383915690560813102681447258323/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage80KernelData.Cell235
