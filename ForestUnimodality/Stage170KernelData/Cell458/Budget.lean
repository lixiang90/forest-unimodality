import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell458.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell458
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(12140212607874969427167497743/100000000000000000000000000000), (184811219248689921118377568569/1000000000000000000000000000000)]
def R : ℚ := (800251808759894459102902374671/1000000000000000000000000000000)
def D : ℚ := (333003813090909090909090909091/200000000000000000000000000000)
def vmax : ℚ := (3177915/12759184)
def mlo : ℚ := (45262373285629099582587954680977/1000000000000000000000000000000)
def mhi : ℚ := (95/2)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (7347051986071724881168284851700946576335193918015905422588888338829197805725192645548005835453/79744900000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (92084677178362817073775659/10000000000000000000000000)) (.exp (-549494834824537599504561071068810928876561137998228932534911/100000000000000000000000000000000000000000000000000000000000) (4107468618029085716283/1000000000000000000000000) (1026867154507271429071/250000000000000000000000) { parts := 6, inner := (-549494834824537599504561071068810928876561137998228932534911/600000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (40018644630592023322452778071/100000000000000000000000000000), innerHi := (400186446305920233224527780711/1000000000000000000000000000000) }))) (.mul (.rat (8709889447213919311252539/100000000000000000000000)) (.exp (-8364994393006445117764131987018279464266285216537819337411913/1000000000000000000000000000000000000000000000000000000000000) (23287833852833187933/100000000000000000000000) (232878338528331879331/1000000000000000000000000) { parts := 9, inner := (-2788331464335481705921377329006093154755428405512606445803971/3000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (98693303429977833450705567599/250000000000000000000000000000), innerHi := (394773213719911333802822270397/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (13279752009198717584623325557634382446551995360530479017176241/167884000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (92084677178362817073775659/10000000000000000000000000)) (.exp (-230664039549624419116182457117/40000000000000000000000000000) (1565189823615223624389/500000000000000000000000) (3130379647230447248779/1000000000000000000000000) { parts := 6, inner := (-230664039549624419116182457117/240000000000000000000000000000), terms := 40, innerLo := (191235936169118205668010879857/500000000000000000000000000000), innerHi := (76494374467647282267204351943/200000000000000000000000000000) }))) (.mul (.rat (8709889447213919311252539/100000000000000000000000)) (.exp (-3511413165725108501249173802811/400000000000000000000000000000) (77001928199458424209/500000000000000000000000) (154003856398916848419/1000000000000000000000000) { parts := 9, inner := (-1170471055241702833749724600937/1200000000000000000000000000000), terms := 40, innerLo := (94261079314465011552861670371/250000000000000000000000000000), innerHi := (75408863451572009242289336297/200000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell458
